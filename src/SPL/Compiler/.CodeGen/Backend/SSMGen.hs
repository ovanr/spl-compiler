{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE GADTs #-}
module SPL.Compiler.CodeGen.Backend.SSMGen where

import Data.Text (Text)
import Data.Map (Map)
import Data.Maybe ( mapMaybe )
import Data.Char (ord)
import Control.Lens ( _tail, view, (%~), traversed )
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad.State ( forM_, execStateT )

import SPL.Compiler.CodeGen.Backend.SSMGenLib (
    SSMMonad, 
    SSMVar(..), 
    Address(..), 
    VarType(..), 
    Register(..), 
    Instruction, 
    loadVarToTopStack, 
    saveTopStackToVar, 
    loadValueToTopStack, 
    loadAddrToTopStack,
    removeStackFrame,
    newBlock, 
    oops,
    output,
    SSMGenState(..),
    addVar,
    getVar)
import qualified SPL.Compiler.CodeGen.Backend.SSMGenLib as SSM
import qualified SPL.Compiler.CodeGen.IRLang as IR
import SPL.Compiler.CodeGen.IRLang (type (-->))
import SPL.Compiler.Common.TypeFunc
    ( hListFromList,
      hListLength,
      hListToList,
      withSome1,
      HList(..),
      Some1(..) )

-- default (Num a) constraints to Num Int when ambiguous from context 
-- default (OpArgument a) constraints to OpArgument Text when ambiguous from context 
default (Int, Text) 


handleInstruction :: IR.IRInstr -> SSMMonad ()
handleInstruction instr =
    case instr of
        IR.Add dst src1 src2 -> handleBinStackOp SSM.add dst src1 src2
        IR.Sub dst src1 src2 -> handleBinStackOp SSM.sub dst src1 src2
        IR.Mul dst src1 src2 -> handleBinStackOp SSM.mul dst src1 src2
        IR.Div dst src1 src2 -> handleBinStackOp SSM.div dst src1 src2
        IR.Mod dst src1 src2 -> handleBinStackOp SSM.mod dst src1 src2
        IR.And dst src1 src2 -> handleBinStackOp SSM.and dst src1 src2
        IR.Or dst src1 src2  -> handleBinStackOp SSM.or  dst src1 src2
        IR.Xor dst src1 src2 -> handleBinStackOp SSM.xor dst src1 src2
        IR.Not dst src       -> handleUnStackOp SSM.not dst src
        IR.Neg dst src       -> handleUnStackOp SSM.neg dst src
        IR.Eq dst src1 src2  -> handleBinStackOp SSM.eq dst src1 src2
        IR.Lt dst src1 src2  -> handleBinStackOp SSM.lt dst src1 src2
        IR.Le dst src1 src2  -> handleBinStackOp SSM.le dst src1 src2
        IR.Gt dst src1 src2  -> handleBinStackOp SSM.gt dst src1 src2
        IR.Ge dst src1 src2  -> handleBinStackOp SSM.ge dst src1 src2
        IR.DeclareTmp _ -> pure () -- handled by `handleFunDef` 
        IR.DeclareV _ -> pure () -- handled by `handleFunDef` 
        IR.SetLabel label -> newBlock label
        IR.BrTrue var label -> do
            loadValueToTopStack var
            SSM.brt label
        IR.BrFalse var label -> do
            loadValueToTopStack var
            SSM.brf label
        IR.BrAlways label -> SSM.bra label
        IR.Call dst fun args -> callFunc dst fun args
        IR.StoreV dst (IR.IRVar src) -> do
            loadVarToTopStack src
            saveTopStackToVar dst
        IR.StoreV dst (IR.IRLit src) -> do
            SSM.ldc src
            saveTopStackToVar dst
        IR.StoreA dst src -> do
            loadValueToTopStack src
            loadVarToTopStack dst 
            SSM.sta 0
        IR.Cast dst src -> do
            loadValueToTopStack src
            saveTopStackToVar dst
        IR.LoadA dst src -> do
            loadVarToTopStack src
            SSM.lda 0
            saveTopStackToVar dst
        IR.Ref dst (IR.Var id _ _) -> do
            (SSMVar _ maddr _) <- getVar id
            case maddr of
                Nothing -> oops $ "Cannot get address of uninitialised variable:" <> id
                (Just addr) -> loadAddrToTopStack addr
            saveTopStackToVar dst
        IR.MkNilList dst -> do
            SSM.ldc 0
            saveTopStackToVar dst
        IR.ConsList dst src1 src2 -> do
            loadValueToTopStack src2
            loadValueToTopStack (IR.IRVar src1)
            SSM.stmh 2
            saveTopStackToVar dst
        IR.MkTup dst src1 src2 -> do
            loadValueToTopStack src1
            loadValueToTopStack src2
            SSM.stmh 2
            saveTopStackToVar dst
        IR.Ret var -> do
            loadValueToTopStack var
            SSM.str RR
            removeStackFrame
        IR.Halt -> SSM.halt
        IR.PrintI var -> do
            loadValueToTopStack var
            SSM.trap 0
        IR.PrintC var -> do
            loadValueToTopStack var
            SSM.trap 1
    where
        handleBinStackOp :: SSMMonad () -> IR.Dst a -> IR.Src1 b -> IR.Src2 b -> SSMMonad ()
        handleBinStackOp op dst src1 src2 = do
            loadValueToTopStack src1
            loadValueToTopStack src2
            op
            saveTopStackToVar dst
        handleUnStackOp :: SSMMonad () -> IR.Dst a -> IR.Src b -> SSMMonad ()
        handleUnStackOp op dst src = do
            loadValueToTopStack src
            op
            saveTopStackToVar dst
        callFunc :: IR.Var r -> IR.Value (IR.Ptr (as --> r)) -> HList IR.Value as -> SSMMonad ()
        callFunc dst (IR.IRLit (IR.IRFun (IR.IRFunDecl label _ _))) args = do
            let numArgs = hListLength args
            forM_ (reverse $ hListToList args) $ \(Some1 arg) -> loadValueToTopStack arg
            SSM.bsr label
            SSM.ajs (-numArgs)
            SSM.ldr RR
            saveTopStackToVar dst
        callFunc dst (IR.IRVar varF) args = do
            let numArgs = hListLength args
            forM_ (reverse $ hListToList args) $ \(Some1 arg) -> loadValueToTopStack arg
            loadVarToTopStack varF
            SSM.jsr
            SSM.ajs (-numArgs)
            SSM.ldr RR
            saveTopStackToVar dst

extractArgsVars :: IR.IRFunDecl as r -> [SSMVar]
extractArgsVars (IR.IRFunDecl _ args _) = extractArgsVars' (-2) args
    where
        extractArgsVars' :: Int -> HList IR.Var xs -> [SSMVar]
        extractArgsVars' offset HNil = []
        extractArgsVars' offset ((IR.Var id _ _) :+: xs) =
            SSMVar id (Just (Address MP offset)) Arg : extractArgsVars' (offset - 1) xs

extractLocalVars :: IR.IRFunDef xs -> [SSMVar]
extractLocalVars (IR.IRFunDef _ instr) =
    withSome1 (hListFromList $ mapMaybe getDeclaredVVar instr) (extractLocalVars' 1)
    where
        getDeclaredVVar :: IR.IRInstr -> Maybe (Some1 IR.Var)
        getDeclaredVVar (IR.DeclareV v) = Just (Some1 v)
        getDeclaredVVar (IR.DeclareTmp v) = Just (Some1 v)
        getDeclaredVVar _ = Nothing

        extractLocalVars' :: Int -> HList IR.Var xs -> [SSMVar]
        extractLocalVars' offset HNil = []
        extractLocalVars' offset ((IR.Var id _ _) :+: xs) =
            SSMVar id (Just (Address MP offset)) Local : extractLocalVars' (offset + 1) xs

handleGlobVarDef :: HList IR.IRGlobal gs -> SSMMonad ()
handleGlobVarDef gs = handleGlobVarDef' 0 gs
    where
        handleGlobVarDef' :: Int -> HList IR.IRGlobal gs -> SSMMonad ()
        handleGlobVarDef' n HNil = pure ()
        handleGlobVarDef' offset ((IR.IRGlobal (IR.Var id _ _)) :+: gs) = do
            let var = SSMVar id (Just (Address GP offset)) Local
            addVar var
            handleGlobVarDef' (offset + 1) gs

handleFunDef :: IR.IRFunDef as -> SSMMonad ()

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "print" _ _)) _) = do
    newBlock "print"
    SSM.link 0
    SSM.ldl (-3)
    SSM.ldl (-2)
    SSM.jsr
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "isEmpty" _ _)) _) = do
    newBlock "isEmpty"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldc 0
    SSM.eq
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "hd" _ _)) _) = do
    newBlock "hd"
    SSM.link 0
    SSM.ldl (-2)
    SSM.lda (-1)
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "_hd_assign" _ _)) _) = do
    newBlock "_hd_assign"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldc 1
    SSM.sub
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "tl" _ _)) _) = do
    newBlock "tl"
    SSM.link 0
    SSM.ldl (-2)
    SSM.lda 0
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "_tl_assign" _ _)) _) = do
    newBlock "_tl_assign"
    SSM.link 0
    SSM.ldl (-2)
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "fst" _ _)) _) = do
    newBlock "fst"
    SSM.link 0
    SSM.ldl (-2)
    SSM.lda (-1)
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "_fst_assign" _ _)) _) = do
    newBlock "_fst_assign"
    SSM.link 0
    SSM.ldl (-2)
    SSM.ldc 1
    SSM.sub
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "snd" _ _)) _) = do
    newBlock "snd"
    SSM.link 0
    SSM.ldl (-2)
    SSM.lda 0
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "_snd_assign" _ _)) _) = do
    newBlock "_snd_assign"
    SSM.link 0
    SSM.ldl (-2)
    SSM.str RR
    removeStackFrame

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "store_thunk" _ _)) _) = do
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

handleFunDef (IR.IRFunDef (IR.IRFunDecl' (IR.IRFunDecl "call_thunk" _ _)) _) = do
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
    SSm.ge 
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

handleFunDef def@(IR.IRFunDef (IR.IRFunDecl' decl@(IR.IRFunDecl label args _)) body) = do
    newBlock label
    let argVars = extractArgsVars decl
    mapM_ addVar argVars
    let locVars = extractLocalVars def
    SSM.link (length locVars)
    mapM_ addVar locVars
    mapM_ handleInstruction body

handleIRLang :: IR.IRLang gs fs -> SSMMonad ()
handleIRLang (IR.IRLang gs fs) = do
    newBlock "_entry"
    SSM.ldrr GP HP
    handleGlobVarDef gs
    SSM.ldc (hListLength gs)
    SSM.ldr HP
    SSM.add
    SSM.str HP
    SSM.bra "_start"
    forM_ (hListToList fs) (\(Some1 def) -> handleFunDef def)

produceSSM :: IR.IRLang gs fs -> Either Text [Text]
produceSSM cl =
    identBlocks . view output
    <$> execStateT (handleIRLang cl) (SSMGenState mempty [])
    where
        identBlocks :: [[Text]] -> [Text]
        identBlocks = concatMap (_tail.traversed %~ ("   " <>))
