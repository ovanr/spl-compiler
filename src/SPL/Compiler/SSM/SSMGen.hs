{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE GADTs #-}
module SPL.Compiler.SSM.SMGen where

import Data.Text (Text)
import Data.Map (Map)
import Data.Maybe ( mapMaybe )
import Data.Char (ord)
import Control.Lens ( _tail, view, (%~), traversed )
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad.State ( forM_, execStateT )

import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SSM.SSMGenLib
import qualified SPL.Compiler.SSM.SSMGenLib as SSM
import SPL.Compiler.Common.TypeFunc

-- default (Num a) constraints to Num Int when ambiguous from context 
-- default (OpArgument a) constraints to OpArgument Text when ambiguous from context 
default (Int, Text) 

coreExprToSSM :: CoreExpr -> SSMMonad ()
coreExprToSSM (IntExpr loc n) = SSM.ldc (fromInteger n :: Int)
coreExprToSSM (CharExpr loc c) = SSM.ldc c
coreExprToSSM (BoolExpr loc b) = SSM.ldc b
coreExprToSSM (FunCallExpr cfc) = _wd
coreExprToSSM (VarIdentifierExpr (CoreIdentifier _ id)) = do
    var <- getVar id 
    loadVarToTopStack var
coreExprToSSM (FunIdentifierExpr ct ci) = _
coreExprToSSM (OpExpr loc UnMinus e) = coreExprToSSM e >> SSM.neg
coreExprToSSM (OpExpr loc UnNeg e) = coreExprToSSM e >> SSM.not
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
        LogAnd -> SSM.and
        LogOr -> SSM.or
        Cons -> SSM.stmh 2
        Pow -> error "pow not implemented"
coreExprToSSM (EmptyListExpr loc ct) = SSM.ldc 0
coreExprToSSM (TupExpr loc e1 e2) = do 
    coreExprToSSM e1
    coreExprToSSM e2
    SSM.stmh 2

coreStmtToSSM :: CoreStmt -> SSMMonad ()
coreStmtToSSM (IfElseStmt _ e taken ntaken) = do
    ifelse <- newLabel "if_else"
    ifend <- newLabel "if_end"
    coreExprToSSM e
    SSM.brf ifelse
    mapM_ coreStmtToSSM taken
    SSM.bra ifend
    mapM_ coreStmtToSSM ntaken
coreStmtToSSM (WhileStmt _ e stmts) = do
    start <- newLabel "while_start"
    end <- newLabel "while_end"
    newBlock start
    coreExprToSSM e
    SSM.brt end
    mapM_ coreStmtToSSM stmts
    SSM.bra start
    newBlock end
coreStmtToSSM (AssignStmt _ ci ct fis ce) = _wm
coreStmtToSSM (FunCallStmt cfc) = _wn
coreStmtToSSM (ReturnStmt _ Nothing) = do
    loadVarToTopStack voidVar
    SSM.str RR
    removeStackFrame
coreStmtToSSM (ReturnStmt _ (Just e)) = do
    coreExprToSSM e
    SSM.str RR
    removeStackFrame

genStoreThunkFun :: SSMMonad ()
genStoreThunkFun = do
    newBlock "store_thunk"
    SSM.link 1
    SSM.ldl (-2)
    SSM.ldc 4
    SSM.add
    SSM.stl 1
    newBlock "store_thunk_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.eq
    SSM.brt "end_store_thunk"
    SSM.ldr MP
    SSM.ldl 1
    SSM.sub
    SSM.lda 0
    SSM.sth
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub
    SSM.stl 1
    SSM.bra "store_thunk_loop"
    newBlock "end_store_thunk"
    SSM.str RR
    removeStackFrame

genCallThunkFun :: SSMMonad ()
genCallThunkFun = do
    newBlock "call_thunk"
    SSM.link 1
    SSM.ldl (-3)
    SSM.stl 1
    newBlock "load_args_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.ge
    SSM.brf "load_thunk"
    SSM.ldr MP 
    SSM.ldl 1
    SSM.sub 
    SSM.lda (-3)
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub 
    SSM.stl 1
    SSM.bra "load_args_loop"
    newBlock "load_thunk"
    SSM.ldl (-2)
    SSM.lda 0
    SSM.ldc 3
    SSM.add 
    SSM.stl 1
    newBlock "load_thunk_loop"
    SSM.ldl 1
    SSM.ldc 1
    SSM.ge 
    SSM.brf "eval_thunk"
    SSM.ldl (-2)
    SSM.ldl 1
    SSM.sub 
    SSM.lda 1
    SSM.ldl 1
    SSM.ldc 1
    SSM.sub 
    SSM.stl 1
    SSM.bra "load_thunk_loop"
    newBlock "eval_thunk"
    SSM.ldl (-3)
    SSM.add 
    SSM.lds (-1)
    SSM.lds (-1)
    SSM.eq 
    SSM.brt "eval_saturated_thunk"
    SSM.bsr "store_thunk"
    removeStackFrame
    newBlock "eval_saturated_thunk"
    SSM.stl 1
    SSM.stl 1
    SSM.jsr
    removeStackFrame
