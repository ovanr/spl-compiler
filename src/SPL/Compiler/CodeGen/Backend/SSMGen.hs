{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE GADTs #-}
module SPL.Compiler.CodeGen.Backend.SSMGen where

import Data.Text (Text)
import Data.Map (Map)
import Data.Maybe
import Data.Char (ord)
import Control.Lens hiding (Snoc, op)
import Data.Function
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad.State

import SPL.Compiler.CodeGen.Backend.SSMGenLib
import qualified SPL.Compiler.CodeGen.CoreLang as C
import SPL.Compiler.CodeGen.CoreLang (type (-->))
import SPL.Compiler.Common.TypeFunc

-- default (Num a) constraints to Num Int when ambiguous from context 
-- default (OpArgument a) constraints to OpArgument Text when ambiguous from context 
default (Int, Text) 

handleInstruction :: C.CoreInstr -> SSMMonad ()
handleInstruction instr =
    case instr of
        C.Add dst src1 src2 -> handleBinStackOp "add" dst src1 src2
        C.Sub dst src1 src2 -> handleBinStackOp "sub" dst src1 src2
        C.Mul dst src1 src2 -> handleBinStackOp "mul" dst src1 src2
        C.Div dst src1 src2 -> handleBinStackOp "div" dst src1 src2
        C.Mod dst src1 src2 -> handleBinStackOp "mod" dst src1 src2
        C.And dst src1 src2 -> handleBinStackOp "and" dst src1 src2
        C.Or dst src1 src2  -> handleBinStackOp "or"  dst src1 src2
        C.Not dst src -> handleUnStackOp "not" dst src
        C.Neg dst src -> handleUnStackOp "neg" dst src
        C.Eq dst src1 src2 -> handleBinStackOp "eq" dst src1 src2
        C.Lt dst src1 src2 -> handleBinStackOp "lt" dst src1 src2
        C.Le dst src1 src2 -> handleBinStackOp "le" dst src1 src2
        C.Gt dst src1 src2 -> handleBinStackOp "gt" dst src1 src2
        C.Ge dst src1 src2 -> handleBinStackOp "ge" dst src1 src2
        C.Declare var -> pure () -- variables are declared upon function entry
        C.SetLabel label -> newBlock label
        C.BrTrue var label -> do
            loadVarToTopStack var
            op1 "brt" label
        C.BrFalse var label -> do
            loadVarToTopStack var
            op1 "brf" label
        C.BrAlways label -> op1 "bra" label
        C.Call dst fun args -> callFunc dst fun args
        C.CallV dst fun args -> callFuncFromVar dst fun args
        C.StoreI dst n -> do
            loadConstantToTopStack n
            saveTopStackToVar dst
        C.StoreC dst c -> do
            loadConstantToTopStack (ord c)
            saveTopStackToVar dst
        C.StoreB dst True -> do
            loadConstantToTopStack (-1)
            saveTopStackToVar dst
        C.StoreB dst False -> do
            loadConstantToTopStack 0
            saveTopStackToVar dst
        C.StoreV dst src -> do
            loadVarToTopStack src
            saveTopStackToVar dst
        C.StoreA dst src -> do
            loadVarToTopStack src
            loadVarToTopStack dst 
            op1 "sta" 0
        C.StoreL dst (C.CoreFunDecl label _ _) -> do
            loadConstantToTopStack label
            saveTopStackToVar dst
        C.StoreVUnsafe dst src -> do
            loadVarToTopStack src
            saveTopStackToVar dst
        C.LoadA dst src -> do
            loadVarToTopStack src
            op1 "lda" 0
            saveTopStackToVar dst
        C.Ref dst (C.Var id _) -> do
            (SSMVar _ addr _) <- getVar id
            loadAddrToTopStack addr
            saveTopStackToVar dst
        C.MkNilList dst -> do
            loadConstantToTopStack 0
            saveTopStackToVar dst
        C.ConsList dst src1 src2 -> do
            loadRegToTopStack HP
            saveTopStackToVar dst
            loadVarToTopStack src2
            op0 "sth"
            loadVarToTopStack src1
            op0 "sth"
            adjustSP (-1)
        C.MkTup dst src1 src2 -> do
            loadRegToTopStack HP
            saveTopStackToVar dst
            loadVarToTopStack src1
            op0 "sth"
            loadVarToTopStack src2
            op0 "sth"
            adjustSP (-1)
        C.RetV var -> do
            loadVarToTopStack var
            saveTopStackToReg RR
            removeStackFrame
        C.Halt -> op0 "halt"
        C.PrintI var -> do
            loadVarToTopStack var
            op1 "trap" 0
        C.PrintC var -> do
            loadVarToTopStack var
            op1 "trap" 1
    where
        handleBinStackOp :: Instruction -> C.Dst a -> C.Src1 b -> C.Src2 b -> SSMMonad ()
        handleBinStackOp op dst src1 src2 = do
            loadVarToTopStack src1
            loadVarToTopStack src2
            op0 op
            saveTopStackToVar dst
        handleUnStackOp :: Instruction -> C.Dst a -> C.Src b -> SSMMonad ()
        handleUnStackOp op dst src = do
            loadVarToTopStack src
            op0 op
            saveTopStackToVar dst
        callFunc :: C.Var r -> C.CoreFunDecl as r -> HList C.Var as -> SSMMonad ()
        callFunc dst (C.CoreFunDecl label _ _) args = do
            let numArgs = hListLength args
            forM_ (reverse $ hListToList args) $ \(Some1 arg) -> loadVarToTopStack arg
            op1 "bsr" label
            adjustSP (-numArgs)
            loadRegToTopStack RR
            saveTopStackToVar dst
        callFuncFromVar :: C.Var r -> C.Var (C.Ptr (as --> r)) -> HList C.Var as -> SSMMonad ()
        callFuncFromVar dst varF args = do
            let numArgs = hListLength args
            forM_ (reverse $ hListToList args) $ \(Some1 arg) -> loadVarToTopStack arg
            loadVarToTopStack varF
            op0 "jsr"
            adjustSP (-numArgs)
            loadRegToTopStack RR
            saveTopStackToVar dst

extractArgsVars :: C.CoreFunDecl as r -> [SSMVar]
extractArgsVars (C.CoreFunDecl _ args _) = extractArgsVars' (-2) args
    where
        extractArgsVars' :: Int -> HList C.Var xs -> [SSMVar]
        extractArgsVars' offset HNil = []
        extractArgsVars' offset ((C.Var id _) :+: xs) =
            SSMVar id (Address MP offset) Arg : extractArgsVars' (offset - 1) xs

extractLocalVars :: C.CoreFunDef xs -> [SSMVar]
extractLocalVars (C.CoreFunDef _ instr) =
    withSome1 (hListFromList $ mapMaybe getDeclaredVar instr) (extractLocalVars' 1)
    where
        getDeclaredVar :: C.CoreInstr -> Maybe (Some1 C.Var)
        getDeclaredVar (C.Declare v) = Just (Some1 v)
        getDeclaredVar _ = Nothing

        extractLocalVars' :: Int -> HList C.Var xs -> [SSMVar]
        extractLocalVars' offset HNil = []
        extractLocalVars' offset ((C.Var id _) :+: xs) =
            SSMVar id (Address MP offset) Local : extractLocalVars' (offset + 1) xs

handleGlobVarDef :: HList C.CoreGlobal gs -> SSMMonad ()
handleGlobVarDef gs = handleGlobVarDef' 0 gs
    where
        handleGlobVarDef' :: Int -> HList C.CoreGlobal gs -> SSMMonad ()
        handleGlobVarDef' n HNil = pure ()
        handleGlobVarDef' offset ((C.CoreGlobal (C.Var id _)) :+: gs) = do
            let var = SSMVar id (Address GP offset) Local
            addVar var
            handleGlobVarDef' (offset + 1) gs

handleFunDef :: C.CoreFunDef as -> SSMMonad ()
handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "isEmpty" _ _)) _) = do
    newBlock "isEmpty"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 0
    op0 "eq"
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "hd" _ _)) _) = do
    newBlock "hd"
    op1 "link" 0
    op1 "ldl" (-2)
    op1 "lda" 0
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "0hd_assign" _ _)) _) = do
    newBlock "0hd_assign"
    op1 "link" 0
    op1 "ldl" (-2)
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "tl" _ _)) _) = do
    newBlock "tl"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 1
    op0 "add"
    op1 "lda" 0
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "0tl_assign" _ _)) _) = do
    newBlock "0tl_assign"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 1
    op0 "add"
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "fst" _ _)) _) = do
    newBlock "fst"
    op1 "link" 0
    op1 "ldl" (-2)
    op1 "lda" 0
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "0fst_assign" _ _)) _) = do
    newBlock "0fst_assign"
    op1 "link" 0
    op1 "ldl" (-2)
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "snd" _ _)) _) = do
    newBlock "snd"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 1
    op0 "add"
    op1 "lda" 0
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "0snd_assign" _ _)) _) = do
    newBlock "0snd_assign"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 1
    op0 "add"
    saveTopStackToReg RR
    removeStackFrame

handleFunDef def@(C.CoreFunDef (C.CoreFunDecl' decl@(C.CoreFunDecl label args _)) body) = do
    newBlock label
    let argVars = extractArgsVars decl
    mapM_ addVar argVars
    let locVars = extractLocalVars def
    op1 "link" (length locVars)
    mapM_ addVar locVars
    mapM_ handleInstruction body

handleCoreLang :: C.CoreLang gs fs -> SSMMonad ()
handleCoreLang (C.CoreLang gs fs) = do
    newBlock "0entry"
    loadRegToTopStack HP
    saveTopStackToReg GP
    handleGlobVarDef gs
    loadConstantToTopStack (hListLength gs)
    loadRegToTopStack HP
    op0 "add"
    saveTopStackToReg HP
    op1 "bra" "0start"
    forM_ (hListToList fs) (\(Some1 def) -> handleFunDef def)

produceSSM :: C.CoreLang gs fs -> Either Text [Text]
produceSSM cl =
    identBlocks . view output
    <$> execStateT (handleCoreLang cl) (SSMGenState mempty [])
    where
        identBlocks :: [[Text]] -> [Text]
        identBlocks = concatMap (_tail.traversed %~ ("   " <>))
