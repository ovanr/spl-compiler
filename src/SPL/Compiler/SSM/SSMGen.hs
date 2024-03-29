{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE GADTs #-}
module SPL.Compiler.SSM.SSMGen where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad.State ( forM_, execStateT )

import SPL.Compiler.SSM.SSMGenLib
import SPL.Compiler.SSM.SSMRuntime
import qualified SPL.Compiler.SSM.SSMGenLib as SSM
import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.Common.Misc (impossible, intercalateM, inSandboxedState)
import Data.Graph (SCC (..))
import Control.Lens (use, traversed, _tail, (%~))
import Control.Lens.Combinators (view)
import Data.Map (Map)
import Data.Maybe (fromJust)
import Control.Lens.Getter ((^.))
import Control.Monad (when)
import Data.List (genericLength)

-- default (Num a) constraints to Num Int when ambiguous from context 
-- default (OpArgument a) constraints to OpArgument Text when ambiguous from context 
default (Int, Text) 

coreFunCallToSSM :: CoreFunCall -> SSMMonad ()
coreFunCallToSSM (CoreFunCall _ (FunIdentifierExpr _ (CoreIdentifier _ id)) _ args) = do
    argSize <- fromJust . M.lookup id <$> use funArgSize 
    if length args == argSize then do
            mapM_ coreExprToSSM (reverse args) 
            SSM.bsr id
            SSM.ajs (-argSize)
            SSM.ldr RR
    else do
        mapM_ coreExprToSSM (reverse args) 
        SSM.ldc id
        SSM.ldc argSize
        SSM.ldc (length args)
        SSM.bsr "__store_thunk"
        SSM.ajs (-(length args + 3))
        SSM.ldr RR
coreFunCallToSSM (CoreFunCall _ e _ args) = do
    mapM_ coreExprToSSM (reverse args) 
    SSM.ldc (length args)
    coreExprToSSM e
    SSM.bsr "__call_thunk"
    SSM.ajs (-(length args + 2))
    SSM.ldr RR

coreExprToSSM :: CoreExpr -> SSMMonad ()
coreExprToSSM (IntExpr loc n) = SSM.ldc (fromInteger n :: Int)
coreExprToSSM (CharExpr loc c) = SSM.ldc c
coreExprToSSM (BoolExpr loc b) = SSM.ldc b
coreExprToSSM (FunCallExpr funCall) = coreFunCallToSSM funCall
coreExprToSSM (VarIdentifierExpr (CoreIdentifier _ id)) = do
    var <- getVar id 
    loadVarToTopStack var
coreExprToSSM (FunIdentifierExpr _ (CoreIdentifier _ id)) = do
    argSize <- fromJust . M.lookup id <$> use funArgSize 
    SSM.ldc id
    SSM.ldc argSize
    SSM.ldc 0
    SSM.bsr "__store_thunk"
    SSM.ajs (-3)
    SSM.ldr RR
coreExprToSSM (OpExpr loc UnMinus e) = coreExprToSSM e >> SSM.neg
coreExprToSSM (OpExpr loc UnNeg e) = coreExprToSSM e >> SSM.not
coreExprToSSM (Op2Expr loc e1 t1 Cons e2 t2) = do
    coreExprToSSM e1
    coreExprToSSM e2
    SSM.stmh 2
coreExprToSSM (Op2Expr loc e1 t1 LogAnd e2 t2) = do 
    lazyAndFalse <- newLabel "lazy_and_false"
    coreExprToSSM e1
    SSM.lds 0
    SSM.brf lazyAndFalse
    coreExprToSSM e2
    SSM.and
    newBlock lazyAndFalse
coreExprToSSM (Op2Expr loc e1 t1 LogOr e2 t2) = do 
    lazyOrTrue <- newLabel "lazy_or_true"
    coreExprToSSM e1
    SSM.lds 0
    SSM.brt lazyOrTrue
    coreExprToSSM e2
    newBlock lazyOrTrue
coreExprToSSM (Op2Expr loc e1 t1 op e2 t2) = do
    coreExprToSSM e1
    coreExprToSSM e2
    case op of
        Plus -> SSM.add
        Minus -> SSM.sub
        Mul -> SSM.mul
        Div -> SSM.div
        Mod -> SSM.mod
        Equal -> SSM.eq 
        Less -> SSM.lt
        Greater -> SSM.gt
        LessEq -> SSM.le
        GreaterEq -> SSM.ge
        Nequal -> SSM.ne
        LogAnd -> impossible
        LogOr -> impossible
        Cons -> impossible
        Pow -> do
            SSM.bsr "_pow"
            SSM.ajs (-2)
            SSM.ldr RR
coreExprToSSM (EmptyListExpr loc ct) = SSM.ldc 0
coreExprToSSM (TupExpr loc e1 e2) = do 
    coreExprToSSM e2
    coreExprToSSM e1
    SSM.stmh 2

countVarDecl :: Integral a => [CoreStmt] -> a
countVarDecl = genericLength . filter isVarDecl 
    where
        isVarDecl (VarDeclStmt _ _) = True
        isVarDecl _ = False

coreStmtToSSM :: CoreStmt -> SSMMonad ()
coreStmtToSSM (IfElseStmt _ e taken ntaken) = do
    ifelse <- newLabel "if_else"
    ifend <- newLabel "if_end"
    coreExprToSSM e
    SSM.brf ifelse
    mapM_ coreStmtToSSM taken
    SSM.ajs (-(countVarDecl taken))
    SSM.bra ifend
    newBlock ifelse
    mapM_ coreStmtToSSM ntaken
    SSM.ajs (-(countVarDecl ntaken))
    newBlock ifend
    SSM.nop
coreStmtToSSM (WhileStmt _ e stmts) = do
    start <- newLabel "while_start"
    end <- newLabel "while_end"
    newBlock start
    coreExprToSSM e
    SSM.brf end
    mapM_ coreStmtToSSM stmts
    SSM.ajs (-(countVarDecl stmts))
    SSM.bra start
    newBlock end
    SSM.nop
coreStmtToSSM (VarDeclStmt offset varDecl@(CoreVarDecl _ _ (CoreIdentifier _ id) e)) = do
    coreExprToSSM e
    let addr = Address MP (fromIntegral $ offset + 1)
    addVar $ SSMVar id (Just addr) SSM.Local

coreStmtToSSM (AssignStmt _ (CoreIdentifier _ id) _ fields e) = do
    coreExprToSSM e
    var <- getVar id
    loadVarAddrToTopStack var
    mapM_ traverseField fields
    SSM.sta 0

    where
        traverseField :: Field -> SSMMonad ()
        traverseField Hd{} = do 
            SSM.lda 0 
            SSM.lds 0 
            SSM.ldc 0 
            SSM.eq 
            SSM.brt "__assign_hd_exception" 
            SSM.ldc 1 
            SSM.sub
        traverseField Tl{} = do 
            SSM.lda 0 
            SSM.lds 0 
            SSM.ldc 0 
            SSM.eq 
            SSM.brt "__assign_tl_exception"
        traverseField Fst{} = SSM.lda 0
        traverseField Snd{} = SSM.lda 0 >> SSM.ldc 1 >> SSM.sub

coreStmtToSSM (FunCallStmt funCall) = coreFunCallToSSM funCall >> SSM.ajs (-1)
coreStmtToSSM (ReturnStmt _ Nothing) = do
    loadVarToTopStack voidVar
    SSM.str RR
    removeStackFrame
coreStmtToSSM (ReturnStmt _ (Just e)) = do
    coreExprToSSM e
    SSM.str RR
    removeStackFrame

coreGlobalVarDeclToSSM :: CoreVarDecl -> SSMMonad ()
coreGlobalVarDeclToSSM (CoreVarDecl _ _ (CoreIdentifier _ id) e) = do
    coreExprToSSM e
    var <- getVar id
    loadVarAddrToTopStack var
    SSM.sta 0

coreFunDeclToSSM :: CoreFunDecl -> SSMMonad ()
coreFunDeclToSSM fun@(CoreFunDecl _ (CoreIdentifier _ id) _ _ (CoreFunBody _ stmts)) = do
    newBlock id
    SSM.nop
    let argVars = extractArgsVars fun
    mapM_ addVar argVars
    SSM.link 0 
    mapM_ coreStmtToSSM stmts
    
coreFunDeclsToSSM :: SCC CoreFunDecl -> SSMMonad ()
coreFunDeclsToSSM (AcyclicSCC fun) = do 
    initialEnv <- use vars
    inSandboxedState vars initialEnv (coreFunDeclToSSM fun)
coreFunDeclsToSSM (CyclicSCC funs) = do
    forM_ funs $ \fun -> do
        initialEnv <- use vars
        inSandboxedState vars initialEnv (coreFunDeclToSSM fun)

declareGlobalVars :: [CoreVarDecl] -> SSMMonad ()
declareGlobalVars varDecls = addVar voidVar >> declareGlobalVars' 1 varDecls
    where
        declareGlobalVars' :: Int -> [CoreVarDecl] -> SSMMonad ()
        declareGlobalVars' n [] = pure ()
        declareGlobalVars' offset (CoreVarDecl _ _ (CoreIdentifier _ id) _:gs) = do
            let var = SSMVar id (Just $ Address GP offset) SSM.Local
            addVar var
            declareGlobalVars' (offset + 1) gs

coreToSSM :: Core -> SSMMonad ()
coreToSSM (Core varDecls funDecls) = do
    newBlock "__entry"
    SSM.ldc 1000
    SSM.ldr HP
    SSM.add
    SSM.str HP
    SSM.ldrr GP HP
    declareGlobalVars varDecls
    SSM.ldc (length varDecls + 1)
    SSM.ldr HP
    SSM.add
    SSM.str HP
    mapM_ coreGlobalVarDeclToSSM varDecls
    when hasMain $ 
        SSM.bsr "main"
    SSM.halt
    mkRuntimeSystem
    forM_ funDecls coreFunDeclsToSSM

    where
        hasMain = "main" `elem` map (^. traversed.funId.idName) funDecls

produceSSM :: Core -> Either Text [Text]
produceSSM core@(Core _ funDecls) =
    identBlocks . view output
    <$> execStateT (coreToSSM core) (SSMGenState mempty 1 mkFunArgSize [])
    where
        identBlocks :: [[Text]] -> [Text]
        identBlocks = concatMap (_tail . traversed %~ ("   " <>))

        builtInsArgSize :: Map Text Int
        builtInsArgSize = M.fromList $
            [("print", 2),
             ("_pow", 2),
             ("isEmpty", 1),
             ("hd", 1),
             ("tl", 1),
             ("fst", 1),
             ("snd", 1),
             ("_print_int", 1),
             ("_print_bool", 1),
             ("_print_char", 1),
             ("_print_char_list", 1),
             ("_print_void", 1),
             ("_print_list", 2),
             ("_print_tup", 3)] ++
             [ ("_" <> tcon <> "_" <> typ, numArgs) 
                | tcon <- ["eq", "lt", "le", "gt", "ge"], 
                  (typ, numArgs) <- [("int", 2), ("bool", 2), ("char", 2), ("void", 2), ("list", 3), ("tup", 4)] ]

        userFunArgSize :: Map Text Int
        userFunArgSize = M.fromList $ concatMap (map userFunArgSizeHelper . unWrap) funDecls
        userFunArgSizeHelper (CoreFunDecl _ (CoreIdentifier _ id) args _ _) = (id, length args)

        mkFunArgSize = userFunArgSize <> builtInsArgSize
        
        unWrap :: SCC a -> [a]
        unWrap (AcyclicSCC a) = [a]
        unWrap (CyclicSCC as) = as
