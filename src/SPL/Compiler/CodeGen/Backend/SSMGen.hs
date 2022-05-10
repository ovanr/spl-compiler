{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
module SPL.Compiler.CodeGen.Backend.SSMGen where


import Data.Text (Text)
import Data.Map (Map)
import Data.Maybe
import Data.Char (ord)
import Control.Lens hiding (Snoc)
import Control.Lens.Combinators
import Data.Function
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad.State
import qualified SPL.Compiler.CodeGen.CoreLang as C
import SPL.Compiler.CodeGen.CoreLang (type (-->))
import SPL.Compiler.Common.TypeFunc

data Register = SP | MP | HP | RR | GP

type Instruction = Text

instance Show Register where
    show SP = "1"
    show MP = "2"
    show HP = "3"
    show RR = "4"
    show GP = "5"

data Address = Address {
    _reg :: Register,
    _offset :: Int
}

makeLenses 'Address

data SSMVar = SSMVar {
    _varName :: Text,
    _varAddress :: Address
}

makeLenses 'SSMVar

data SSMGenState = SSMGenState {
    _vars :: Map Text [SSMVar],
    _output :: [[Text]]
}

makeLenses 'SSMGenState

type SSMMonad a = StateT SSMGenState (Either Text) a

oops :: Text -> SSMMonad a
oops err = lift (Left err)

write :: [Text] -> SSMMonad ()
write instr = modify $ \st -> st & output._last <>~ instr

newBlock :: Text -> SSMMonad ()
newBlock label = modify $ \st -> st & output <>~ [[label <> ":"]]

getVar :: Text -> SSMMonad SSMVar
getVar id = do
    varMap <- use vars
    case M.lookup id varMap of
        Nothing -> oops $ "Variable " <> id <> " not declared"
        Just [] -> oops $ "Variable " <> id <> " no longer available"
        Just (x:_) -> pure x

addVar :: SSMVar -> SSMMonad ()
addVar var@(SSMVar id _) = modify (\st -> st & vars %~ M.insertWith (++) id [var])

loadRegToTopStack :: Register -> SSMMonad ()
loadRegToTopStack reg = write ["ldr " <> T.pack (show reg)]

loadVarToTopStack :: C.Var a -> SSMMonad ()
loadVarToTopStack (C.Var id _) = do
    var <- getVar id
    case var ^. varAddress of
        Address MP offset -> write ["ldl " <> T.pack (show offset)]
        Address reg offset -> loadRegToTopStack reg >> write ["lda " <> T.pack (show offset)]

saveTopStackToVar :: C.Var a -> SSMMonad ()
saveTopStackToVar (C.Var id _) = do
    var <- getVar id
    case var ^. varAddress of
        Address MP offset -> write ["stl " <> T.pack (show offset)]
        Address reg offset -> loadRegToTopStack reg >> write ["sta " <> T.pack (show offset)]

loadConstant :: Int -> SSMMonad ()
loadConstant i = write ["ldc " <> T.pack (show i)]

loadAddrToTopStack :: Address -> SSMMonad ()
loadAddrToTopStack (Address reg offset) = do
    loadRegToTopStack reg
    loadConstant offset
    write ["add"]

handleInstruction :: C.CoreInstr -> SSMMonad ()
handleInstruction instr =
    case instr of
        C.Add dst src1 src2 -> handleBinOp "add" dst src1 src2
        C.Sub dst src1 src2 -> handleBinOp "sub" dst src1 src2
        C.Mul dst src1 src2 -> handleBinOp "mul" dst src1 src2
        C.Div dst src1 src2 -> handleBinOp "div" dst src1 src2
        C.Mod dst src1 src2 -> handleBinOp "mod" dst src1 src2
        C.And dst src1 src2 -> handleBinOp "and" dst src1 src2
        C.Or dst src1 src2  -> handleBinOp "or"  dst src1 src2
        C.Not dst src -> handleUnOp "not" dst src
        C.Neg dst src -> handleUnOp "neg" dst src
        C.Eq dst src1 src2 -> handleBinOp "eq" dst src1 src2
        C.Lt dst src1 src2 -> handleBinOp "lt" dst src1 src2
        C.Le dst src1 src2 -> handleBinOp "le" dst src1 src2
        C.Gt dst src1 src2 -> handleBinOp "gt" dst src1 src2
        C.Ge dst src1 src2 -> handleBinOp "ge" dst src1 src2
        C.Declare var -> pure () -- variables are declared upon function entry
        C.SetLabel label -> newBlock label
        C.BrTrue var label -> do
            loadVarToTopStack var
            write ["brt " <> label]
        C.BrFalse var label -> do
            loadVarToTopStack var
            write ["brf " <> label]
        C.BrAlways label -> write ["bra " <> label]
        C.Call dst fun args -> callFunc dst fun args
        C.CallV dst fun args -> callFuncFromVar dst fun args
        C.StoreI dst n -> do
            loadConstant n
            saveTopStackToVar dst
        C.StoreC dst c -> do
            loadConstant (ord c)
            saveTopStackToVar dst
        C.StoreB dst True -> do
            loadConstant (-1)
            saveTopStackToVar dst
        C.StoreB dst False -> do
            loadConstant 0
            saveTopStackToVar dst
        C.StoreV dst src -> do
            loadVarToTopStack src
            saveTopStackToVar dst
        C.StoreA dst src -> do
            loadVarToTopStack src
            loadVarToTopStack dst
            write ["sta 0"]
        C.StoreL dst (C.CoreFunDecl label _ _) -> do
            write ["ldc " <> label]
            saveTopStackToVar dst
        C.StoreVUnsafe _ _ -> pure ()
        C.LoadA dst src -> do
            loadVarToTopStack src
            write ["lda 0"]
            saveTopStackToVar dst
        C.Ref dst (C.Var id _) -> do
            (SSMVar _ addr) <- getVar id
            loadAddrToTopStack addr
            saveTopStackToVar dst
        C.MkNilList dst -> do
            loadConstant 0
            saveTopStackToVar dst
        C.ConsList dst src1 src2 -> do
            loadVarToTopStack src2
            write ["sth"]
            saveTopStackToVar dst
            loadVarToTopStack src1
            write ["sth"]
            loadConstant 1
            write ["add"]
            write ["str " <> T.pack (show HP)]
        C.MkTup dst src1 src2 -> do
            loadVarToTopStack src1
            write ["sth"]
            saveTopStackToVar dst
            loadVarToTopStack src2
            write ["sth"]
            loadConstant 1
            write ["add"]
            write ["str " <> T.pack (show HP)]
        C.RetV var -> do
            loadVarToTopStack var
            write ["str " <> T.pack (show RR)]
            write ["unlink"]
            write ["ret"]
        C.Halt -> write ["halt"]
        C.PrintI var -> do
            loadVarToTopStack var
            write ["trap 0"]
        C.PrintC var -> do
            loadVarToTopStack var
            write ["trap 1"]
    where
        handleBinOp :: Instruction -> C.Dst a -> C.Src1 b -> C.Src2 b -> SSMMonad ()
        handleBinOp op dst src1 src2 = do
            loadVarToTopStack src1
            loadVarToTopStack src2
            write [op]
            saveTopStackToVar dst
        handleUnOp :: Instruction -> C.Dst a -> C.Src b -> SSMMonad ()
        handleUnOp op dst src = do
            loadVarToTopStack src
            write [op]
            saveTopStackToVar dst
        callFunc :: C.Var r -> C.CoreFunDecl as r -> HList C.Var as -> SSMMonad ()
        callFunc dst (C.CoreFunDecl label _ _) args = do
            let numArgs = hListLength args
            forM_ (hListToList args) $ \(Some1 arg) -> loadVarToTopStack arg
            write ["bsr " <> label]
            when (numArgs > 0) $
                write ["ajs " <> T.pack (show (-numArgs))]
            loadRegToTopStack RR
            saveTopStackToVar dst
        callFuncFromVar :: C.Var r -> C.Var (C.Ptr (as --> r)) -> HList C.Var as -> SSMMonad ()
        callFuncFromVar dst varF args = do
            let numArgs = hListLength args
            forM_ (hListToList args) $ \(Some1 arg) -> loadVarToTopStack arg
            loadVarToTopStack varF
            write ["jsr"]
            when (numArgs > 0) $
                write ["ajs " <> T.pack (show (-numArgs))]
            loadRegToTopStack RR
            saveTopStackToVar dst

extractArgsVars :: C.CoreFunDecl as r -> [SSMVar]
extractArgsVars (C.CoreFunDecl _ args _) = extractArgsVars' (-2) args
    where
        extractArgsVars' :: Int -> HList C.Var xs -> [SSMVar]
        extractArgsVars' offset HNil = []
        extractArgsVars' offset ((C.Var id _) :+: xs) =
            SSMVar id (Address MP offset) : extractArgsVars' (offset - 1) xs

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
            SSMVar id (Address MP offset) : extractLocalVars' (offset + 1) xs

handleFunDef :: C.CoreFunDef as -> SSMMonad ()
handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "isEmpty" _ _)) _) = do
    newBlock "isEmpty"
    write ["link 0"]
    loadConstant 0
    write ["eq"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "hd" _ _)) _) = do
    newBlock "hd"
    write ["link 0"]
    write ["ldl -2"]
    write ["lda 0"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "0hd_assign" _ _)) _) = do
    newBlock "0hd_assign"
    write ["link 0"]
    write ["ldl -2"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "tl" _ _)) _) = do
    newBlock "tl"
    write ["link 0"]
    write ["ldl -2"]
    loadConstant 1
    write ["add"]
    write ["lda 0"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "0tl_assign" _ _)) _) = do
    newBlock "0tl_assign"
    write ["link 0"]
    write ["ldl -2"]
    loadConstant 1
    write ["add"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "fst" _ _)) _) = do
    newBlock "fst"
    write ["link 0"]
    write ["ldl -2"]
    write ["lda 0"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "0fst_assign" _ _)) _) = do
    newBlock "0fst_assign"
    write ["link 0"]
    write ["ldl -2"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "snd" _ _)) _) = do
    newBlock "snd"
    write ["link 0"]
    write ["ldl -2"]
    loadConstant 1
    write ["add"]
    write ["lda 0"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef (C.CoreFunDef (C.CoreFunDecl' (C.CoreFunDecl "0snd_assign" _ _)) _) = do
    newBlock "0snd_assign"
    write ["link 0"]
    write ["ldl -2"]
    loadConstant 1
    write ["add"]
    write ["str " <> T.pack (show RR)]
    write ["unlink"]
    write ["ret"]

handleFunDef def@(C.CoreFunDef (C.CoreFunDecl' decl@(C.CoreFunDecl label args _)) body) = do
    newBlock label
    let argVars = extractArgsVars decl
    mapM_ addVar argVars
    let locVars = extractLocalVars def
    write ["link " <> T.pack (show $ length locVars)]
    mapM_ addVar locVars
    mapM_ handleInstruction body

handleCoreLang :: C.CoreLang gs fs -> SSMMonad ()
handleCoreLang (C.CoreLang _ fs) = do
    forM_ (hListToList fs) (\(Some1 def) -> handleFunDef def)

produceSSM :: C.CoreLang gs fs -> Either Text [Text]
produceSSM cl = concatMap (_tail.traversed %~ ("   " <>)) <$> evalStateT (handleCoreLang cl >> use output) (SSMGenState mempty [])
