{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
module SPL.Compiler.CodeGen.Backend.SSMGenLib where

import Data.Text (Text)
import Data.Map (Map)
import Data.Maybe
import Data.Char (ord)
import Control.Lens hiding (Snoc)
import Data.Function
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad.State

import qualified SPL.Compiler.CodeGen.IRLang as IR
import SPL.Compiler.CodeGen.IRLang (type (-->))
import SPL.Compiler.Common.TypeFunc

data Register = SP | MP | HP | RR | GP deriving Show

type Instruction = Text

getRegValue :: Register -> Int
getRegValue SP = 1
getRegValue MP = 2
getRegValue HP = 3
getRegValue RR = 4
getRegValue GP = 5

data Address = Address {
    _reg :: Register,
    _offset :: Int
}

makeLenses 'Address

data VarType = Arg | Local deriving Eq

data SSMVar = SSMVar {
    _varName :: Text,
    _varAddress :: Address,
    _varType :: VarType
}

makeLenses 'SSMVar

data SSMGenState = SSMGenState {
    _vars :: Map Text [SSMVar],
    _output :: [[Text]]
}

makeLenses 'SSMGenState

type SSMMonad a = StateT SSMGenState (Either Text) a

class OpArgument a where
    toArgument :: a -> Text

instance OpArgument Int where
    toArgument = T.pack . show

instance OpArgument String where
    toArgument = T.pack

instance OpArgument Text where
    toArgument = id

oops :: Text -> SSMMonad a
oops err = lift (Left err)

write :: [Text] -> SSMMonad ()
write instr = modify $ \st -> st & output._last <>~ instr

newBlock :: Text -> SSMMonad ()
newBlock label = modify $ \st -> st & output <>~ [[label <> ": nop"]]

getVar :: Text -> SSMMonad SSMVar
getVar id = do
    varMap <- use vars
    case M.lookup id varMap of
        Nothing -> oops $ "Variable " <> id <> " not declared"
        Just [] -> oops $ "Variable " <> id <> " no longer available"
        Just (x:_) -> pure x

addVar :: SSMVar -> SSMMonad ()
addVar var@(SSMVar id _ _) = modify (\st -> st & vars %~ M.insertWith (++) id [var])

loadRegToTopStack :: Register -> SSMMonad ()
loadRegToTopStack reg = write ["ldr " <> T.pack (show $ getRegValue reg)]

saveTopStackToReg :: Register -> SSMMonad ()
saveTopStackToReg reg = write ["str " <> T.pack (show $ getRegValue reg)]

annotate :: SSMVar -> SSMMonad ()
annotate (SSMVar id (Address reg offset) varType) = do
    let reg' = T.pack (show reg)
        loc = T.pack (show offset)
        color = if varType == Arg then "red" else "blue"
    write [T.unwords ["annote", reg', loc, loc, color, "\"" <> id <> "\""]]

loadVarToTopStack :: IR.Var a -> SSMMonad ()
loadVarToTopStack (IR.Var id _) = do
    var <- getVar id
    annotate var 
    case var ^. varAddress of
        Address MP offset -> write ["ldl " <> T.pack (show offset)]
        Address reg offset -> loadRegToTopStack reg >> write ["lda " <> T.pack (show offset)]

saveTopStackToVar :: IR.Var a -> SSMMonad ()
saveTopStackToVar (IR.Var id _) = do
    var <- getVar id
    annotate var 
    case var ^. varAddress of
        Address MP offset -> write ["stl " <> T.pack (show offset)]
        Address reg offset -> loadRegToTopStack reg >> write ["sta " <> T.pack (show offset)]

adjustSP :: Int -> SSMMonad ()
adjustSP 0 = pure ()
adjustSP n = op1 "ajs" n

loadConstantToTopStack :: OpArgument a => a -> SSMMonad ()
loadConstantToTopStack i = write ["ldc " <> toArgument i]

loadAddrToTopStack :: Address -> SSMMonad ()
loadAddrToTopStack (Address reg offset) = do
    loadRegToTopStack reg
    loadConstantToTopStack offset
    write ["add"]

op0 :: Instruction -> SSMMonad ()
op0 instruction = write [instruction]

op1 :: OpArgument a => Instruction -> a -> SSMMonad ()
op1 instruction arg = write [instruction <> " " <> toArgument arg]

removeStackFrame :: SSMMonad ()
removeStackFrame = write ["unlink", "ret"]
