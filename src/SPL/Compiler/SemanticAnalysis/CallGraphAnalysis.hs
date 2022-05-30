{-# LANGUAGE TupleSections #-}

module SPL.Compiler.SemanticAnalysis.CallGraphAnalysis (
    reorderAst
    ) where

import Data.Graph
import Data.Maybe
import Data.Either
import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.State

import SPL.Compiler.Parser.AST
import Control.Applicative (liftA2)
import Options.Applicative (liftA3)

type CGState a = State [FunName] a
type FunName = Text
type FunId = Int
-- function name (FunName) must be unique for each function declaration
type CallGraph = [(ASTFunDecl, FunName, [FunName])]

getFunNames :: [ASTFunDecl] -> [FunName]
getFunNames = map (\(ASTFunDecl _ (ASTIdentifier _ id) _ _ _) -> id)

astToCallGraph :: AST -> CallGraph
astToCallGraph (ASTUnordered leaves) = 
    let funDecls = rights leaves
        state = getFunNames funDecls
    in concatMap (flip evalState state . astFunToCallGraph) funDecls

astToCallGraph ASTOrdered{} = error "AST is already reordered"

astFunToCallGraph :: ASTFunDecl -> CGState CallGraph
astFunToCallGraph f@(ASTFunDecl _ (ASTIdentifier _ id) _ _ (ASTFunBody _ vars stmts)) =
    pure . (f, id,) <$> 
        liftA2 (++)
            (concat <$> mapM funCallInVarDecl vars) 
            (concat <$> mapM funCallInStmt stmts)

funCallInVarDecl :: ASTVarDecl -> CGState [FunName]
funCallInVarDecl (ASTVarDecl _ _ (ASTIdentifier _ id) e) = do 
    r <- funCallInExpr e
    modify (filter (/= id))
    pure r

funCallInStmt :: ASTStmt -> CGState [FunName]
funCallInStmt (IfElseStmt _ e s1 s2) =
    liftA3 (\a b c -> a ++ b ++ c) 
        (funCallInExpr e)
        (concat <$> mapM funCallInStmt s1) 
        (concat <$> mapM funCallInStmt s2)
funCallInStmt (WhileStmt _ e s) = liftA2 (++) (funCallInExpr e) (concat <$> mapM funCallInStmt s)
funCallInStmt (AssignStmt _ _ _ e) = funCallInExpr e
funCallInStmt (FunCallStmt f) = funCallInFunCall f
funCallInStmt (ReturnStmt _ me) = maybe (pure []) funCallInExpr me

funCallInExpr :: ASTExpr -> CGState [FunName]
funCallInExpr (IdentifierExpr (ASTIdentifier _ id)) = do
    funcs <- get
    if id `elem` funcs then pure [id] else pure []
funCallInExpr (FunCallExpr f) = funCallInFunCall f
funCallInExpr (FieldSelectExpr _ e _) = funCallInExpr e
funCallInExpr (OpExpr _ _ e) = funCallInExpr e
funCallInExpr (Op2Expr _ e1 _ e2) = liftA2 (++) (funCallInExpr e1) (funCallInExpr e2)
funCallInExpr (TupExpr _ e1 e2) = liftA2 (++) (funCallInExpr e1) (funCallInExpr e2)
funCallInExpr _ = pure []

funCallInFunCall :: ASTFunCall -> CGState [FunName]
funCallInFunCall (ASTFunCall _ e args) = 
    liftA2 (++) (funCallInExpr e) (concat <$> mapM funCallInExpr args)

callGraph2ast :: AST -> CallGraph -> AST
callGraph2ast ASTOrdered{} _ = error "AST is already reordered"
callGraph2ast (ASTUnordered leaves) g =
    ASTOrdered (lefts leaves) scc

    where
        scc :: [SCC ASTFunDecl]
        scc = stronglyConnComp g

reorderAst :: AST -> AST
reorderAst ast@ASTUnordered{} = callGraph2ast ast $ astToCallGraph ast
reorderAst ast@ASTOrdered{} = ast
