
module SPL.Compiler.SemanticAnalysis.CallGraphAnalysis (
    reorderTct
    ) where

import Data.Graph
import Data.Maybe
import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as M

import SPL.Compiler.SemanticAnalysis.TCT

type FunName = Text
type FunId = Int
-- function name (FunName) must be unique for each function declaration
type CallGraph = [(TCTFunDecl, FunName, [FunName])]

tctToCallGraph :: TCT -> CallGraph
tctToCallGraph (TCT _ funDecls) = concatMap (concatMap tctFunToCallGraph) funDecls

tctFunToCallGraph :: TCTFunDecl -> CallGraph
tctFunToCallGraph f@(TCTFunDecl _ (TCTIdentifier _ id) _ _ _ (TCTFunBody _ vars stmts)) =
    [(f, id, concatMap funCallInVarDecl vars <> concatMap funCallInStmt stmts)]

funCallInVarDecl :: TCTVarDecl -> [FunName]
funCallInVarDecl (TCTVarDecl _ _ _ e) = funCallInExpr e

funCallInStmt :: TCTStmt -> [FunName]
funCallInStmt (IfElseStmt _ e s1 s2) =
    funCallInExpr e <> concatMap funCallInStmt s1 <> concatMap funCallInStmt s2
funCallInStmt (WhileStmt _ e s) = funCallInExpr e <> concatMap funCallInStmt s
funCallInStmt (AssignStmt _ _ e) = funCallInExpr e
funCallInStmt (FunCallStmt _ f) = funCallInFunCall f
funCallInStmt (ReturnStmt _ me) = maybe [] funCallInExpr me

funCallInExpr :: TCTExpr -> [FunName]
funCallInExpr (FunCallExpr f) = funCallInFunCall f
funCallInExpr (OpExpr _ _ e) = funCallInExpr e
funCallInExpr (Op2Expr _ e1 _ e2) = funCallInExpr e1 <> funCallInExpr e2
funCallInExpr (TupExpr _ e1 e2) = funCallInExpr e1 <> funCallInExpr e2
funCallInExpr _ = []

funCallInFunCall :: TCTFunCall -> [FunName]
funCallInFunCall (TCTFunCall _ (TCTIdentifier _ id) _ _ args) = id : concatMap funCallInExpr args

callGraph2Tct :: TCT -> CallGraph -> TCT
callGraph2Tct prevTct@(TCT varDecls funDecls) g =
    TCT varDecls (map toFunDecls scc)

    where
        toFunDecls :: SCC TCTFunDecl -> [TCTFunDecl]
        toFunDecls (AcyclicSCC f) = [f]
        toFunDecls (CyclicSCC fs) = fs

        scc :: [SCC TCTFunDecl]
        scc = stronglyConnComp g

reorderTct :: TCT -> TCT
reorderTct tct = callGraph2Tct tct $ tctToCallGraph tct
