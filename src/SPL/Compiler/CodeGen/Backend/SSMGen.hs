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
import qualified SPL.Compiler.CodeGen.IRLang as IR
import SPL.Compiler.CodeGen.IRLang (type (-->))
import SPL.Compiler.Common.TypeFunc

-- default (Num a) constraints to Num Int when ambiguous from context 
-- default (OpArgument a) constraints to OpArgument Text when ambiguous from context 
default (Int, Text) 

handleInstruction :: IR.IRInstr -> SSMMonad ()
handleInstruction instr =
    case instr of
        IR.Add dst src1 src2 -> handleBinStackOp "add" dst src1 src2
        IR.Sub dst src1 src2 -> handleBinStackOp "sub" dst src1 src2
        IR.Mul dst src1 src2 -> handleBinStackOp "mul" dst src1 src2
        IR.Div dst src1 src2 -> handleBinStackOp "div" dst src1 src2
        IR.Mod dst src1 src2 -> handleBinStackOp "mod" dst src1 src2
        IR.And dst src1 src2 -> handleBinStackOp "and" dst src1 src2
        IR.Or dst src1 src2  -> handleBinStackOp "or"  dst src1 src2
        IR.Not dst src -> handleUnStackOp "not" dst src
        IR.Neg dst src -> handleUnStackOp "neg" dst src
        IR.Eq dst src1 src2 -> handleBinStackOp "eq" dst src1 src2
        IR.Lt dst src1 src2 -> handleBinStackOp "lt" dst src1 src2
        IR.Le dst src1 src2 -> handleBinStackOp "le" dst src1 src2
        IR.Gt dst src1 src2 -> handleBinStackOp "gt" dst src1 src2
        IR.Ge dst src1 src2 -> handleBinStackOp "ge" dst src1 src2
        IR.Declare var -> pure () -- variables are declared upon function entry
        IR.SetLabel label -> newBlock label
        IR.BrTrue var label -> do
            loadVarToTopStack var
            op1 "brt" label
        IR.BrFalse var label -> do
            loadVarToTopStack var
            op1 "brf" label
        IR.BrAlways label -> op1 "bra" label
        IR.Call dst fun args -> callFunc dst fun args
        IR.CallV dst fun args -> callFuncFromVar dst fun args
        IR.StoreI dst n -> do
            loadConstantToTopStack n
            saveTopStackToVar dst
        IR.StoreC dst c -> do
            loadConstantToTopStack (ord c)
            saveTopStackToVar dst
        IR.StoreB dst True -> do
            loadConstantToTopStack (-1)
            saveTopStackToVar dst
        IR.StoreB dst False -> do
            loadConstantToTopStack 0
            saveTopStackToVar dst
        IR.StoreV dst src -> do
            loadVarToTopStack src
            saveTopStackToVar dst
        IR.StoreA dst src -> do
            loadVarToTopStack src
            loadVarToTopStack dst 
            op1 "sta" 0
        IR.StoreL dst (IR.IRFunDecl label _ _) -> do
            loadConstantToTopStack label
            saveTopStackToVar dst
        IR.StoreVUnsafe dst src -> do
            loadVarToTopStack src
            saveTopStackToVar dst
        IR.LoadA dst src -> do
            loadVarToTopStack src
            op1 "lda" 0
            saveTopStackToVar dst
        IR.Ref dst (IR.Var id _) -> do
            (SSMVar _ addr _) <- getVar id
            loadAddrToTopStack addr
            saveTopStackToVar dst
        IR.MkNilList dst -> do
            loadConstantToTopStack 0
            saveTopStackToVar dst
        IR.ConsList dst src1 src2 -> do
            loadRegToTopStack HP
            saveTopStackToVar dst
            loadVarToTopStack src2
            op0 "sth"
            loadVarToTopStack src1
            op0 "sth"
            adjustSP (-1)
        IR.MkTup dst src1 src2 -> do
            loadRegToTopStack HP
            saveTopStackToVar dst
            loadVarToTopStack src1
            op0 "sth"
            loadVarToTopStack src2
            op0 "sth"
            adjustSP (-1)
        IR.RetV var -> do
            loadVarToTopStack var
            saveTopStackToReg RR
            removeStackFrame
        IR.Halt -> op0 "halt"
        IR.PrintI var -> do
            loadVarToTopStack var
            op1 "trap" 0
        IR.PrintC var -> do
            loadVarToTopStack var
            op1 "trap" 1
    where
        handleBinStackOp :: Instruction -> IR.Dst a -> IR.Src1 b -> IR.Src2 b -> SSMMonad ()
        handleBinStackOp op dst src1 src2 = do
            loadVarToTopStack src1
            loadVarToTopStack src2
            op0 op
            saveTopStackToVar dst
        handleUnStackOp :: Instruction -> IR.Dst a -> IR.Src b -> SSMMonad ()
        handleUnStackOp op dst src = do
            loadVarToTopStack src
            op0 op
            saveTopStackToVar dst
        callFunc :: IR.Var r -> IR.IRFunDecl as r -> HList IR.Var as -> SSMMonad ()
        callFunc dst (IR.IRFunDecl label _ _) args = do
            let numArgs = hListLength args
            forM_ (reverse $ hListToList args) $ \(Some1 arg) -> loadVarToTopStack arg
            op1 "bsr" label
            adjustSP (-numArgs)
            loadRegToTopStack RR
            saveTopStackToVar dst
        callFuncFromVar :: IR.Var r -> IR.Var (IR.Ptr (as --> r)) -> HList IR.Var as -> SSMMonad ()
        callFuncFromVar dst varF args = do
            let numArgs = hListLength args
            forM_ (reverse $ hListToList args) $ \(Some1 arg) -> loadVarToTopStack arg
            loadVarToTopStack varF
            op0 "jsr"
            adjustSP (-numArgs)
            loadRegToTopStack RR
            saveTopStackToVar dst

extractArgsVars :: IR.IRFunDecl as r -> [SSMVar]
extractArgsVars (IR.IRFunDecl _ args _) = extractArgsVars' (-2) args
    where
        extractArgsVars' :: Int -> HList IR.Var xs -> [SSMVar]
        extractArgsVars' offset HNil = []
        extractArgsVars' offset ((IR.Var id _) :+: xs) =
            SSMVar id (Address MP offset) Arg : extractArgsVars' (offset - 1) xs

extractLocalVars :: IR.IRFunDef xs -> [SSMVar]
extractLocalVars (IR.IRFunDef _ instr) =
    withSome1 (hListFromList $ mapMaybe getDeclaredVar instr) (extractLocalVars' 1)
    where
        getDeclaredVar :: IR.IRInstr -> Maybe (Some1 IR.Var)
        getDeclaredVar (IR.Declare v) = Just (Some1 v)
        getDeclaredVar _ = Nothing

        extractLocalVars' :: Int -> HList IR.Var xs -> [SSMVar]
        extractLocalVars' offset HNil = []
        extractLocalVars' offset ((IR.Var id _) :+: xs) =
            SSMVar id (Address MP offset) Local : extractLocalVars' (offset + 1) xs

handleGlobVarDef :: HList IR.IRGlobal gs -> SSMMonad ()
handleGlobVarDef gs = handleGlobVarDef' 0 gs
    where
        handleGlobVarDef' :: Int -> HList IR.IRGlobal gs -> SSMMonad ()
        handleGlobVarDef' n HNil = pure ()
        handleGlobVarDef' offset ((IR.IRGlobal (IR.Var id _)) :+: gs) = do
            let var = SSMVar id (Address GP offset) Local
            addVar var
            handleGlobVarDef' (offset + 1) gs

handleFunDef :: IR.IRFunDef as -> SSMMonad ()
handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "isEmpty" _ _)) _) = do
    newBlock "isEmpty"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 0
    op0 "eq"
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "hd" _ _)) _) = do
    newBlock "hd"
    op1 "link" 0
    op1 "ldl" (-2)
    op1 "lda" 0
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "0hd_assign" _ _)) _) = do
    newBlock "0hd_assign"
    op1 "link" 0
    op1 "ldl" (-2)
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "tl" _ _)) _) = do
    newBlock "tl"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 1
    op0 "add"
    op1 "lda" 0
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "0tl_assign" _ _)) _) = do
    newBlock "0tl_assign"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 1
    op0 "add"
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "fst" _ _)) _) = do
    newBlock "fst"
    op1 "link" 0
    op1 "ldl" (-2)
    op1 "lda" 0
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "0fst_assign" _ _)) _) = do
    newBlock "0fst_assign"
    op1 "link" 0
    op1 "ldl" (-2)
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "snd" _ _)) _) = do
    newBlock "snd"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 1
    op0 "add"
    op1 "lda" 0
    saveTopStackToReg RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "0snd_assign" _ _)) _) = do
    newBlock "0snd_assign"
    op1 "link" 0
    op1 "ldl" (-2)
    loadConstantToTopStack 1
    op0 "add"
    saveTopStackToReg RR
    removeStackFrame

handleFunDef def@(IR.IRFunDef (IR.IRFunDecl' decl@(IR.IRFunDecl label args _)) body) = do
    newBlock label
    let argVars = extractArgsVars decl
    mapM_ addVar argVars
    let locVars = extractLocalVars def
    op1 "link" (length locVars)
    mapM_ addVar locVars
    mapM_ handleInstruction body

handleIRLang :: IR.IRLang gs fs -> SSMMonad ()
handleIRLang (IR.IRLang gs fs) = do
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

produceSSM :: IR.IRLang gs fs -> Either Text [Text]
produceSSM cl =
    identBlocks . view output
    <$> execStateT (handleIRLang cl) (SSMGenState mempty [])
    where
        identBlocks :: [[Text]] -> [Text]
        identBlocks = concatMap (_tail.traversed %~ ("   " <>))
