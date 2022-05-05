{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
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
        funId,
        funArgs,
        funVars,
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
import Control.Lens (makeLenses)

import SPL.Compiler.Common.TypeFunc

data Var a = Var {
    _varIdentifier :: Identifier, 
    _varType :: CoreType a
}

type Identifier = Text
type Label = Text
type Unit = ()
type Dst a = Var a
type Src a = Var a
type Src1 a = Var a
type Src2 a = Var a
data Ptr a
data Unknown

data CoreLang gs fs = CoreLang (HList CoreGlobal gs) (HList CoreFunDef fs)

data CoreGlobal a = CoreGlobal (Var a) [CoreInstr]

data CoreFunDecl' xs where
    CoreFunDecl' :: CoreFunDecl as vs r -> CoreFunDecl' (Snoc as r)

data CoreFunDecl as vs r = CoreFunDecl {
        _funId :: Label,
        _funArgs :: HList Var as,
        _funVars :: HList Var vs, 
        _funRetType :: CoreType r
    }

data CoreFunDef xs = CoreFunDef {
    _funDecl :: CoreFunDecl' xs,
    _funBody :: [CoreInstr]
}

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
    Declare :: Var a -> CoreInstr
    SetLabel :: Label -> CoreInstr
    BrTrue :: Var Bool -> Label -> CoreInstr
    BrFalse :: Var Bool -> Label -> CoreInstr
    BrAlways :: Label -> CoreInstr
    Call :: Dst r -> CoreFunDecl as vs r -> HList Var as -> CoreInstr
    StoreI :: Dst Int -> Int -> CoreInstr
    StoreC :: Dst Char -> Char -> CoreInstr
    StoreB :: Dst Bool -> Bool -> CoreInstr
    StoreV :: Dst a -> Src a -> CoreInstr
    StoreA :: Dst (Ptr a) -> Src a -> CoreInstr
    StoreVUnsafe :: Dst b -> Src a -> CoreInstr
    LoadA :: Dst a -> Src (Ptr a) -> CoreInstr
    Ref :: Dst (Ptr a) -> Src a -> CoreInstr
    MkNilList :: Dst (Ptr [a]) -> CoreInstr
    ConsList :: Dst (Ptr [a]) -> Src1 (Ptr [a]) -> Src2 a -> CoreInstr
    MkTup :: Dst (Ptr (a, b)) -> Src1 a -> Src2 b -> CoreInstr
    RetV :: Var a -> CoreInstr

data CoreType a where
    CoreIntType :: CoreType Int 
    CoreBoolType :: CoreType Bool
    CoreCharType :: CoreType Char
    CoreVoidType :: CoreType Unit
    CoreUnknownType :: CoreType Unknown
    CorePtrType :: CoreType a -> CoreType (Ptr a)
    CoreListType :: CoreType a -> CoreType (Ptr [a])
    CoreFunType :: CoreType a -> CoreType b -> CoreType (Ptr (a -> b))
    CoreTupleType :: CoreType a -> CoreType b -> CoreType (Ptr (a, b))

hasUnknownType :: CoreType a -> Bool
hasUnknownType (CorePtrType _) = True
hasUnknownType (CoreListType ct) = hasUnknownType ct
hasUnknownType (CoreTupleType cta ctb) = hasUnknownType cta || hasUnknownType ctb
hasUnknownType (CoreFunType cta ctb) = hasUnknownType cta || hasUnknownType ctb
hasUnknownType _ = False

instance Show (CoreType a) where
    show CoreIntType = "%i"
    show CoreBoolType = "%b"
    show CoreCharType = "%c"
    show CoreVoidType = "%1"
    show CoreUnknownType = "%?"
    show (CorePtrType a) = "&(" <> show a <> ")"
    show (CoreListType a) = "&[" <> show a <> "]"
    show (CoreTupleType a b) = "&(" <> show a <> "," <> show b <> ")"
    show (CoreFunType a b) = "&(" <> show a <> "->" <> show b <> ")"

makeLenses ''CoreFunDecl
makeLenses ''CoreFunDef
makeLenses ''Var
