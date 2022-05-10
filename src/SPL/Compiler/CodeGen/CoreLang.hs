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

module SPL.Compiler.CodeGen.CoreLang (
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
        CoreLang(..),
        CoreFunDecl(..),
        CoreFunDef(..),
        toCoreType,
        type (-->),
        CollapseFunType,
        funId,
        funArgs,
        funRetType,
        funBody,
        varIdentifier,
        varType,
        hasUnknownType,
        CoreFunDecl'(..),
        CoreGlobal(..),
        CoreInstr(..),
        CoreType(..)
    ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import Control.Lens (makeLenses)
import Data.Proxy

import SPL.Compiler.Common.TypeFunc

data Var a = Var {
    _varIdentifier :: Identifier,
    _varType :: CoreType a
}

instance Show (Var a) where
    show (Var id t) = T.unpack id <> "%" <> show t
    
type Identifier = Text
type Label = Text
type Unit = ()
type Dst a = Var a
type Src a = Var a
type Src1 a = Var a
type Src2 a = Var a
data Ptr a
data (-->) (a :: [*]) r
data Unknown

data CoreLang gs fs = CoreLang (HList CoreGlobal gs) (HList CoreFunDef fs)

data CoreGlobal a = CoreGlobal (Var a) [CoreInstr]

data CoreFunDecl' xs where
    CoreFunDecl' :: CoreFunDecl as r -> CoreFunDecl' (Snoc as r)

data CoreFunDecl as r = CoreFunDecl {
        _funId :: Identifier,
        _funArgs :: HList Var as,
        _funRetType :: CoreType r
    }

data CoreFunDef xs = CoreFunDef {
    _funDecl :: CoreFunDecl' xs,
    _funBody :: [CoreInstr]
}

type family CollapseFunType (a :: *) :: [*] where 
    CollapseFunType (Ptr (as --> r)) = Snoc as r
    CollapseFunType a = '[a]

data CoreInstr where
    Add :: Dst Int -> Src1 Int -> Src2 Int -> CoreInstr
    Sub :: Dst Int -> Src1 Int -> Src2 Int -> CoreInstr
    Mul :: Dst Int -> Src1 Int -> Src2 Int -> CoreInstr
    Div :: Dst Int -> Src1 Int -> Src2 Int -> CoreInstr
    Mod :: Dst Int -> Src1 Int -> Src2 Int -> CoreInstr
    And :: Dst Bool -> Src1 Bool -> Src2 Bool -> CoreInstr
    Or :: Dst Bool -> Src1 Bool -> Src2 Bool -> CoreInstr
    Not :: Dst Bool -> Src Bool -> CoreInstr
    Neg :: Dst Int -> Src Int -> CoreInstr
    Eq :: Dst Bool -> Src1 Int -> Src2 Int -> CoreInstr
    Lt :: Dst Bool -> Src1 Int -> Src2 Int -> CoreInstr
    Le :: Dst Bool -> Src1 Int -> Src2 Int -> CoreInstr
    Gt :: Dst Bool -> Src1 Int -> Src2 Int -> CoreInstr
    Ge :: Dst Bool -> Src1 Int -> Src2 Int -> CoreInstr
    Declare :: Var a -> CoreInstr
    SetLabel :: Label -> CoreInstr
    BrTrue :: Var Bool -> Label -> CoreInstr
    BrFalse :: Var Bool -> Label -> CoreInstr
    BrAlways :: Label -> CoreInstr
    Call :: Dst r -> CoreFunDecl as r -> HList Var as -> CoreInstr
    CallV :: Dst r -> Src (Ptr (as --> r)) -> HList Var as -> CoreInstr
    StoreI :: Dst Int -> Int -> CoreInstr
    StoreC :: Dst Char -> Char -> CoreInstr
    StoreB :: Dst Bool -> Bool -> CoreInstr
    StoreV :: Dst a -> Src a -> CoreInstr
    StoreA :: Dst (Ptr a) -> Src a -> CoreInstr
    StoreL :: Dst (Ptr (as --> r)) -> CoreFunDecl as r -> CoreInstr
    StoreVUnsafe :: Dst b -> Src a -> CoreInstr
    LoadA :: Dst a -> Src (Ptr a) -> CoreInstr
    Ref :: Dst (Ptr a) -> Src a -> CoreInstr
    MkNilList :: Dst (Ptr [a]) -> CoreInstr
    ConsList :: Dst (Ptr [a]) -> Src1 (Ptr [a]) -> Src2 a -> CoreInstr
    MkTup :: Dst (Ptr (a, b)) -> Src1 a -> Src2 b -> CoreInstr
    RetV :: Var a -> CoreInstr
    Halt :: CoreInstr
    PrintI :: Var Int -> CoreInstr
    PrintC :: Var Char -> CoreInstr

data CoreType a where
    CoreIntType :: CoreType Int
    CoreBoolType :: CoreType Bool
    CoreCharType :: CoreType Char
    CoreVoidType :: CoreType Unit
    CoreUnknownType :: Text -> CoreType Unknown
    CorePtrType :: CoreType a -> CoreType (Ptr a)
    CoreListType :: CoreType a -> CoreType (Ptr [a])
    CoreFunType :: HList CoreType as -> CoreType r -> CoreType (Ptr (as --> r))
    CoreTupleType :: CoreType a -> CoreType b -> CoreType (Ptr (a, b))

class FromHaskellType a where
    fromHaskellType :: Proxy a -> CoreType a
    
instance FromHaskellType Int where
    fromHaskellType _ = CoreIntType

instance FromHaskellType Bool where
    fromHaskellType _ = CoreBoolType

instance FromHaskellType Char where
    fromHaskellType _ = CoreCharType

instance FromHaskellType () where
    fromHaskellType _ = CoreVoidType

instance FromHaskellType Unknown where
    fromHaskellType _ = CoreUnknownType ""

instance FromHaskellType a => FromHaskellType (Ptr [a]) where
    fromHaskellType _ = CoreListType (fromHaskellType (Proxy @a))

instance (FromHaskellType a, FromHaskellType b) => FromHaskellType (Ptr (a,b)) where
    fromHaskellType _ = CoreTupleType (fromHaskellType (Proxy @a)) (fromHaskellType (Proxy @b))

instance (ConstrMap FromHaskellType xs, HListFromProxy xs, FromHaskellType r) => FromHaskellType (Ptr (xs --> r)) where
    fromHaskellType _ = CoreFunType 
        (hListFromHaskellType $ hListFromProxy (Proxy @xs)) 
        (fromHaskellType (Proxy @r))
        where
            hListFromHaskellType :: forall xs. ConstrMap FromHaskellType xs => HList Proxy xs -> HList CoreType xs
            hListFromHaskellType HNil = HNil
            hListFromHaskellType (x :+: xs) = fromHaskellType x :+: hListFromHaskellType xs

toCoreType :: forall a. FromHaskellType a => CoreType a
toCoreType = fromHaskellType (Proxy @a)

type CoreTCon a = CoreType (Ptr ('[a, a] --> Bool))
type CoreTOrd a = CoreType (Ptr ('[a, a] --> Bool))
type CoreTPrint a = CoreType (Ptr ('[a] --> Unit))
    
hasUnknownType :: CoreType a -> Bool
hasUnknownType (CoreUnknownType _) = True
hasUnknownType (CorePtrType ct) = hasUnknownType ct
hasUnknownType (CoreListType ct) = hasUnknownType ct
hasUnknownType (CoreTupleType cta ctb) = hasUnknownType cta || hasUnknownType ctb
hasUnknownType (CoreFunType cta ctb) =
    hListFoldl (\acc t -> acc || hasUnknownType t) False cta || hasUnknownType ctb
hasUnknownType _ = False

instance Show (CoreType a) where
    show CoreIntType = "i"
    show CoreBoolType = "b"
    show CoreCharType = "c"
    show CoreVoidType = "v"
    show (CoreUnknownType var) = "?" 
    show (CorePtrType a) = "*(" <> show a <> ")"
    show (CoreListType a) = "*[" <> show a <> "]"
    show (CoreTupleType a b) = "*(" <> show a <> "," <> show b <> ")"
    show (CoreFunType as r) = 
        "*(" <> L.intercalate "->" (hListMapToList show as) <> "->" <> show r <> ")"

makeLenses ''CoreFunDecl
makeLenses ''CoreFunDef
makeLenses ''Var
