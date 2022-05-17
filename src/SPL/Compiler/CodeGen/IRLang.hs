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
        Var(..),
        IRLang(..),
        IRFunDecl(..),
        IRFunDef(..),
        toIRType,
        type (-->),
        CollapseFunType,
        funId,
        funArgs,
        funRetType,
        funBody,
        varIdentifier,
        varType,
        hasUnknownType,
        IRFunDecl'(..),
        IRGlobal(..),
        IRInstr(..),
        IRType(..)
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

data Var a = Var {
    _varIdentifier :: Identifier,
    _varType :: IRType a
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
    Add :: Dst Int -> Src1 Int -> Src2 Int -> IRInstr
    Sub :: Dst Int -> Src1 Int -> Src2 Int -> IRInstr
    Mul :: Dst Int -> Src1 Int -> Src2 Int -> IRInstr
    Div :: Dst Int -> Src1 Int -> Src2 Int -> IRInstr
    Mod :: Dst Int -> Src1 Int -> Src2 Int -> IRInstr
    And :: Dst Bool -> Src1 Bool -> Src2 Bool -> IRInstr
    Or :: Dst Bool -> Src1 Bool -> Src2 Bool -> IRInstr
    Not :: Dst Bool -> Src Bool -> IRInstr
    Neg :: Dst Int -> Src Int -> IRInstr
    Eq :: Dst Bool -> Src1 Int -> Src2 Int -> IRInstr
    Lt :: Dst Bool -> Src1 Int -> Src2 Int -> IRInstr
    Le :: Dst Bool -> Src1 Int -> Src2 Int -> IRInstr
    Gt :: Dst Bool -> Src1 Int -> Src2 Int -> IRInstr
    Ge :: Dst Bool -> Src1 Int -> Src2 Int -> IRInstr
    Declare :: Var a -> IRInstr
    SetLabel :: Label -> IRInstr
    BrTrue :: Var Bool -> Label -> IRInstr
    BrFalse :: Var Bool -> Label -> IRInstr
    BrAlways :: Label -> IRInstr
    Call :: Dst r -> Value (Ptr (as --> r)) -> HList Var as -> IRInstr
    StoreI :: Dst Int -> Int -> IRInstr
    StoreC :: Dst Char -> Char -> IRInstr
    StoreB :: Dst Bool -> Bool -> IRInstr
    StoreV :: Dst a -> Src a -> IRInstr
    StoreA :: Dst (Ptr a) -> Src a -> IRInstr
    StoreVUnsafe :: Dst b -> Src a -> IRInstr
    LoadA :: Dst a -> Src (Ptr a) -> IRInstr
    Ref :: Dst (Ptr a) -> Src a -> IRInstr
    MkNilList :: Dst (Ptr [a]) -> IRInstr
    ConsList :: Dst (Ptr [a]) -> Src1 (Ptr [a]) -> Src2 a -> IRInstr
    MkTup :: Dst (Ptr (a, b)) -> Src1 a -> Src2 b -> IRInstr
    RetV :: Var a -> IRInstr
    Halt :: IRInstr
    PrintI :: Var Int -> IRInstr
    PrintC :: Var Char -> IRInstr

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
    IRInt :: Int -> IRConstant Int
    IRBool :: Bool -> IRConstant Bool 
    IRChar :: Char -> IRConstant Char 
    IRFun :: IRFunDecl as r -> IRConstant (Ptr (as --> r)) 

class FromHaskellType a where
    fromHaskellType :: Proxy a -> IRType a
    
instance FromHaskellType Int where
    fromHaskellType _ = IRIntType

instance FromHaskellType Bool where
    fromHaskellType _ = IRBoolType

instance FromHaskellType Char where
    fromHaskellType _ = IRCharType

instance FromHaskellType () where
    fromHaskellType _ = IRVoidType

instance FromHaskellType Unknown where
    fromHaskellType _ = IRUnknownType ""

instance FromHaskellType a => FromHaskellType (Ptr [a]) where
    fromHaskellType _ = IRListType (fromHaskellType (Proxy @a))

instance (FromHaskellType a, FromHaskellType b) => FromHaskellType (Ptr (a,b)) where
    fromHaskellType _ = IRTupleType (fromHaskellType (Proxy @a)) (fromHaskellType (Proxy @b))

instance (ConstrMap FromHaskellType xs, HListFromProxy xs, FromHaskellType r) => FromHaskellType (Ptr (xs --> r)) where
    fromHaskellType _ = IRFunType 
        (hListFromHaskellType $ hListFromProxy (Proxy @xs)) 
        (fromHaskellType (Proxy @r))
        where
            hListFromHaskellType :: forall xs. ConstrMap FromHaskellType xs => HList Proxy xs -> HList IRType xs
            hListFromHaskellType HNil = HNil
            hListFromHaskellType (x :+: xs) = fromHaskellType x :+: hListFromHaskellType xs

toIRType :: forall a. FromHaskellType a => IRType a
toIRType = fromHaskellType (Proxy @a)
    
hasUnknownType :: IRType a -> Bool
hasUnknownType (IRUnknownType _) = True
hasUnknownType (IRPtrType ct) = hasUnknownType ct
hasUnknownType (IRListType ct) = hasUnknownType ct
hasUnknownType (IRTupleType cta ctb) = hasUnknownType cta || hasUnknownType ctb
hasUnknownType (IRFunType cta ctb) =
    hListFoldl (\acc t -> acc || hasUnknownType t) False cta || hasUnknownType ctb
hasUnknownType _ = False

instance Show (Var a) where
    show (Var id t) = T.unpack id <> "%" <> show t

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
