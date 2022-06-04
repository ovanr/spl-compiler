{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module SPL.Compiler.SSM.SSMGenLib where

import Data.Text (Text)
import Data.Map (Map)
import Data.Maybe
import Data.Char (ord)
import Control.Lens hiding (Snoc)
import Data.Function
import Numeric.Natural
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.Map as M
import Control.Monad.State

import SPL.Compiler.Common.TypeFunc
import SPL.Compiler.SemanticAnalysis.Core (CoreFunDecl(..), CoreIdentifier (..), CoreFunBody (..), CoreVarDecl (..))

default (Int, Text)

data Register = SP | MP | HP | RR | GP deriving (Show, Eq)

type Instruction = Text

data Address = Address {
    _reg :: Register,
    _offset :: Int
} deriving Eq

makeLenses 'Address

data VarType = Arg | Local deriving Eq

data SSMVar = SSMVar {
    _varName :: Text,
    _varAddress :: Maybe Address,
    _varType :: VarType
} deriving Eq


makeLenses 'SSMVar

data SSMGenState = SSMGenState {
    _vars :: Map Text [SSMVar],
    _counter :: Int,
    _output :: [[Text]]
}

makeLenses 'SSMGenState

type SSMMonad a = StateT SSMGenState (Either Text) a

class OpArgument a where
    toArgument :: a -> Text

instance OpArgument Bool where
    toArgument True = T.pack $ show (-1 :: Int)
    toArgument False = T.pack $ show (0 :: Int)

instance OpArgument Char where
    toArgument = T.pack . show . ord

instance OpArgument Int where
    toArgument = T.pack . show

instance OpArgument String where
    toArgument = T.pack

instance OpArgument Text where
    toArgument = id

instance OpArgument Register where
    toArgument SP = "1"
    toArgument MP = "2"
    toArgument HP = "3"
    toArgument RR = "4"
    toArgument GP = "5"

voidVar = SSMVar "_void_var" (Just (Address GP 0)) Local

newLabel :: Text -> SSMMonad Text
newLabel prefix = do
    c <- T.pack . show <$> use counter
    let label = "__" <> prefix <> c
    pure label

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

loadVarToTopStack :: SSMVar -> SSMMonad ()
loadVarToTopStack var@(SSMVar id address _) = do
    annotate var
    case var ^. varAddress of
        Just (Address MP offset) -> op1 "ldl" offset
        Just (Address reg offset) -> ldr reg >> lda offset
        Nothing -> oops $ "Variable " <> id <> " address not available"

loadVarAddrToTopStack :: SSMVar -> SSMMonad ()
loadVarAddrToTopStack var@(SSMVar id address _) = do
    annotate var
    case var ^. varAddress of
        Just (Address reg offset) -> ldr MP >> ldc offset >> add
        Nothing -> oops $ "Variable " <> id <> " address not available"


addVar :: SSMVar -> SSMMonad ()
addVar var@(SSMVar id _ _) = modify (\st -> st & vars %~ M.insertWith (++) id [var])

replaceVar :: SSMVar -> SSMVar -> SSMMonad ()
replaceVar fromVar@(SSMVar id _ _) toVar =
    vars %= (at id %~ fmap (traversed.filtered (== fromVar) .~ toVar))

removeVar :: SSMVar -> SSMMonad ()
removeVar fromVar@(SSMVar id _ _) =
    vars %= (at id %~ fmap (^.. traversed.filtered (fromVar /=)))

extractArgsVars :: CoreFunDecl -> [SSMVar]
extractArgsVars (CoreFunDecl _ _ args _ _) = extractArgsVars' (-2) args
    where
        extractArgsVars' :: Int -> [CoreIdentifier] -> [SSMVar]
        extractArgsVars' offset [] = []
        extractArgsVars' offset (CoreIdentifier _ id:xs) =
            SSMVar id (Just (Address MP offset)) Arg : extractArgsVars' (offset - 1) xs

extractLocalVars :: CoreFunDecl -> [SSMVar]
extractLocalVars (CoreFunDecl _ _ _ _ (CoreFunBody _ varDecls _)) = 
    extractLocalVars' 1 varDecls
    where
        extractLocalVars' :: Int -> [CoreVarDecl] -> [SSMVar]
        extractLocalVars' offset [] = []
        extractLocalVars' offset (CoreVarDecl _ _ (CoreIdentifier _ id) _: xs) =
            SSMVar id (Just (Address MP offset)) Local : extractLocalVars' (offset + 1) xs

annotate :: SSMVar -> SSMMonad ()
annotate (SSMVar _ Nothing _) = pure ()
annotate (SSMVar id (Just (Address reg offset)) varType) = do
    let reg' = T.pack (show reg)
        loc = T.pack (show offset)
        color = if varType == Arg then "red" else "blue"
    write [T.unwords ["annote", reg', loc, loc, color, "\"" <> id <> "\""]]

loadAddrToTopStack :: Address -> SSMMonad ()
loadAddrToTopStack (Address reg offset) = do
    ldr reg
    case offset of
        0 -> pure ()
        n -> ldc offset >> add

op0 :: Instruction -> SSMMonad ()
op0 instruction = write [instruction]

op1 :: Instruction -> OpArgument a => a -> SSMMonad ()
op1 instruction arg = do
    write [instruction <> " " <> toArgument arg]

op2 :: Instruction -> OpArgument a => a -> OpArgument b => b -> SSMMonad ()
op2 instruction arg1 arg2 = do
    write [instruction <> " " <> toArgument arg1 <> " " <> toArgument arg2]

removeStackFrame :: SSMMonad ()
removeStackFrame = unlink >> ret

-- ldc lds ldms sts stms ldsa ldl ldml stl stml ldla lda ldma ldaa 
-- sta stma ldr ldrr str swp swpr swprr bsr bra brf brt jsr ret 
-- link unlink nop halt trap annote ldh ldmh sth stmh

ldc :: OpArgument a => a -> SSMMonad ()
ldc = op1 "ldc"

ajs :: Int -> SSMMonad ()
ajs 0 = pure ()
ajs n = op1 "ajs" n

link :: Int -> SSMMonad ()
link = op1 "link"

unlink :: SSMMonad ()
unlink = op0 "unlink"

ret :: SSMMonad ()
ret = op0 "ret"

ldr :: Register -> SSMMonad ()
ldr = op1 "ldr"

ldrr :: Register -> Register -> SSMMonad ()
ldrr = op2 "ldrr"

str :: Register -> SSMMonad ()
str = op1 "str"

sta :: Int -> SSMMonad ()
sta = op1 "sta"

lda :: Int -> SSMMonad ()
lda = op1 "lda"

add = op0 "add"
sub = op0 "sub"
mul = op0 "mul"
div = op0 "div"
mod = op0 "mod"
and = op0 "and"
or  = op0 "or"
xor = op0 "xor"
eq  = op0 "eq"
ne  = op0 "ne"
lt  = op0 "lt"
le  = op0 "le"
gt  = op0 "gt"
ge  = op0 "ge"
not = op0 "not"
neg = op0 "neg"

brt :: OpArgument a => a -> SSMMonad ()
brt = op1 "brt"

brf :: OpArgument a => a -> SSMMonad ()
brf = op1 "brf"

bra :: OpArgument a => a -> SSMMonad ()
bra = op1 "bra"

sth :: SSMMonad ()
sth = op0 "sth"

stmh :: OpArgument a => a -> SSMMonad ()
stmh = op1 "stmh"

bsr :: OpArgument a => a -> SSMMonad ()
bsr = op1 "bsr"
jsr = op0 "jsr"

trap :: OpArgument a => a -> SSMMonad ()
trap = op1 "trap"

halt = op0 "halt"

stl :: Int -> SSMMonad ()
stl = op1 "stl"

ldl :: Int -> SSMMonad ()
ldl = op1 "ldl"

lds :: Int -> SSMMonad ()
lds = op1 "lds"
