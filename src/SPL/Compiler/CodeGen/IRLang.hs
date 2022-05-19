{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SPL.Compiler.CodeGen.IRLang (
        Identifier,
        Label,
        Unit,
        Dst,
        Src,
        Src1,
        Src2,
        Ptr,
        Unknown,
        Value(..),
        Var(..),
        VarKind(..),
        IRConstant(..),
        IRLang(..),
        IRFunDecl(..),
        IRFunDef(..),
        type (-->),
        CollapseFunType,
        Castable,
        funId,
        funArgs,
        funRetType,
        funBody,
        varIdentifier,
        varType,
        IRFunDecl'(..),
        IRGlobal(..),
        IRInstr(..),
        IRType(..),
        Typeable(..)
    ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import Control.Lens (makeLenses)
import Data.Proxy

import SPL.Compiler.Common.TypeFunc

type Identifier = Text
type Label = Text
type Unit = ()
type Dst a = Var a
type Src a = Value a
type Src1 a = Value a
type Src2 a = Value a
data Ptr a
data (-->) (a :: [*]) r
data Unknown

data VarKind = Temp | Declared

data Var a = Var {
    _varIdentifier :: Identifier,
    _varType :: IRType a,
    _varKind :: VarKind
}
data Value a = IRVar (Var a) | IRLit (IRConstant a)

data IRLang gs fs = IRLang (HList IRGlobal gs) (HList IRFunDef fs)

newtype IRGlobal a = IRGlobal (Var a)

data IRFunDecl' xs where
    IRFunDecl' :: IRFunDecl as r -> IRFunDecl' (Snoc as r)

data IRFunDecl as r = IRFunDecl {
        _funId :: Identifier,
        _funArgs :: HList Var as,
        _funRetType :: IRType r
    }

data IRFunDef xs = IRFunDef {
    _funDecl :: IRFunDecl' xs,
    _funBody :: [IRInstr]
}

type family CollapseFunType (a :: *) :: [*] where
    CollapseFunType (Ptr (as --> r)) = Snoc as r
    CollapseFunType a = '[a]

data IRInstr where
    Add :: Var Int -> Value Int -> Value Int -> IRInstr
    Sub :: Var Int -> Value Int -> Value Int -> IRInstr
    Mul :: Var Int -> Value Int -> Value Int -> IRInstr
    Div :: Var Int -> Value Int -> Value Int -> IRInstr
    Mod :: Var Int -> Value Int -> Value Int -> IRInstr
    And :: Var Bool -> Value Bool -> Value Bool -> IRInstr
    Or :: Var Bool -> Value Bool -> Value Bool -> IRInstr
    Xor :: Var Bool -> Value Bool -> Value Bool -> IRInstr
    Not :: Var Bool -> Value Bool -> IRInstr
    Neg :: Var Int -> Value Int -> IRInstr
    Eq :: Var Bool -> Value Int -> Value Int -> IRInstr
    Lt :: Var Bool -> Value Int -> Value Int -> IRInstr
    Le :: Var Bool -> Value Int -> Value Int -> IRInstr
    Gt :: Var Bool -> Value Int -> Value Int -> IRInstr
    Ge :: Var Bool -> Value Int -> Value Int -> IRInstr
    DeclareV :: Var a -> IRInstr
    DeclareTmp :: Var a -> IRInstr
    SetLabel :: Label -> IRInstr
    BrTrue :: Value Bool -> Label -> IRInstr
    BrFalse :: Value Bool -> Label -> IRInstr
    BrAlways :: Label -> IRInstr
    Call :: Var r -> Value (Ptr (as --> r)) -> HList Value as -> IRInstr
    StoreV :: Var a -> Value a -> IRInstr
    StoreA :: Var (Ptr a) -> Value a -> IRInstr
    Cast :: forall a b. Castable a b => Var b -> Value a -> IRInstr
    LoadA :: Var a -> Var (Ptr a) -> IRInstr
    Ref :: Var (Ptr a) -> Var a -> IRInstr
    MkNilList :: Var (Ptr [a]) -> IRInstr
    ConsList :: Var (Ptr [a]) -> Var (Ptr [a]) -> Value a -> IRInstr
    MkTup :: Var (Ptr (a, b)) -> Value a -> Value b -> IRInstr
    Ret :: Value a -> IRInstr
    Halt :: IRInstr
    PrintI :: Value Int -> IRInstr
    PrintC :: Value Char -> IRInstr

data IRType a where
    IRIntType :: IRType Int
    IRBoolType :: IRType Bool
    IRCharType :: IRType Char
    IRVoidType :: IRType Unit
    IRUnknownType :: Text -> IRType Unknown
    IRPtrType :: IRType a -> IRType (Ptr a)
    IRListType :: IRType a -> IRType (Ptr [a])
    IRFunType :: HList IRType as -> IRType r -> IRType (Ptr (as --> r))
    IRTupleType :: IRType a -> IRType b -> IRType (Ptr (a, b))

data IRConstant a where
    IRVoid :: IRConstant Unit
    IRInt :: Int -> IRConstant Int
    IRBool :: Bool -> IRConstant Bool
    IRChar :: Char -> IRConstant Char
    IRFun :: IRFunDecl as r -> IRConstant (Ptr (as --> r))

class Castable a b

instance Castable Bool Int
instance Castable Char Int
instance {-# INCOHERENT #-} Castable a Unknown
instance Castable Unknown a
instance {-# OVERLAPPABLE #-} Castable a b => Castable (Ptr a) (Ptr b)
instance {-# OVERLAPS #-} Castable a b => Castable (Ptr [a]) (Ptr [b])
instance {-# OVERLAPS #-} (Castable a1 a2, Castable b1 b2) => Castable (Ptr (a1,b1)) (Ptr (a2,b2))
instance Castable '[] '[]
instance (Castable x y, Castable xs ys) =>
         Castable (x ': xs) (y ': ys)
instance {-# OVERLAPS #-} (Castable as1 as2, Castable r1 r2) =>
         Castable (Ptr (as1 --> r1)) (Ptr (as2 --> r2))

class Typeable f where
    getType :: f a -> IRType a
    setType :: f a -> IRType b -> f b

instance Show (Var a) where
    show (Var id t _) = T.unpack id <> "%" <> show t

instance Show (IRType a) where
    show IRIntType = "i"
    show IRBoolType = "b"
    show IRCharType = "c"
    show IRVoidType = "v"
    show (IRUnknownType var) = "?"
    show (IRPtrType a) = "*(" <> show a <> ")"
    show (IRListType a) = "*[" <> show a <> "]"
    show (IRTupleType a b) = "*(" <> show a <> "," <> show b <> ")"
    show (IRFunType as r) =
        "*(" <> L.intercalate "->" (hListMapToList show as) <> "->" <> show r <> ")"

makeLenses ''IRFunDecl
makeLenses ''IRFunDef
makeLenses ''Var
