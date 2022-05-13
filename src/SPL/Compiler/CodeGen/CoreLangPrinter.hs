{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module SPL.Compiler.CodeGen.CoreLangPrinter where

import Data.Text (Text)
import qualified Data.Text as T

import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.Common.TypeFunc

mkIdent :: Int -> Text
mkIdent n = foldl (<>) "" $ replicate n "   "

class CoreLangPrinter a where
    showCL :: Int -> a -> Text

instance CoreLangPrinter Int where
    showCL _ i = T.pack (show i)

instance CoreLangPrinter Bool where
    showCL _ b = T.pack (show b)

instance CoreLangPrinter Char where
    showCL _ c = T.pack (show c)

instance CoreLangPrinter Label where
    showCL ident l = mkIdent ident <> l

instance CoreLangPrinter (CoreType a) where
    showCL _ t = T.pack (show t)

instance CoreLangPrinter (Var a) where
    showCL _ (Var id t) = id <> "%" <> showCL 0 t

instance CoreLangPrinter (HList Var xs) where
    showCL _ = T.intercalate " " . hListMapToList (showCL 0)

instance CoreLangPrinter (CoreLang gs fs) where 
    showCL ident (CoreLang globals funcs) = 
        showCL ident globals <> "\n" <> showCL ident funcs

instance CoreLangPrinter (HList CoreGlobal gs) where
    showCL ident = T.intercalate "\n" . hListMapToList (showCL 0)

instance CoreLangPrinter (CoreGlobal a) where
    showCL ident (CoreGlobal var) = "GLOBAL " <> showCL ident var

instance CoreLangPrinter (HList CoreFunDecl' gs) where
    showCL ident = T.intercalate "\n" . hListMapToList (showCL 0)

instance CoreLangPrinter (CoreFunDef xs) where
    showCL ident (CoreFunDef decl body) = 
        showCL ident decl <> "\n" <> showCL (ident + 2) body

instance CoreLangPrinter (HList CoreFunDef gs) where
    showCL ident = T.intercalate "\n" . hListMapToList (showCL 0)

instance CoreLangPrinter (CoreFunDecl' xs) where
    showCL ident (CoreFunDecl' decl) = showCL ident decl

instance CoreLangPrinter (CoreFunDecl as r) where
    showCL ident (CoreFunDecl label args retType) =
        mkIdent ident <> showCL 0 label <> 
            "(" <> showCL 0 args <> ") %" <> showCL 0 retType <> ":"

instance CoreLangPrinter [CoreInstr] where
    showCL ident = T.unlines . map (showCL ident)

instance CoreLangPrinter CoreInstr where
    showCL ident (Add dst src1 src2) =
        mkIdent ident <> "Add " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Sub dst src1 src2) =
        mkIdent ident <> "Sub " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Mul dst src1 src2) =
        mkIdent ident <> "Mul " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Div dst src1 src2) =
        mkIdent ident <> "Div " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Mod dst src1 src2) =
        mkIdent ident <> "Mod " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (And dst src1 src2) =
        mkIdent ident <> "And " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Or dst src1 src2) =
        mkIdent ident <> "Or " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Not dst src) =
        mkIdent ident <> "Not " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (Neg dst src) =
        mkIdent ident <> "Neg " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (Eq dst src1 src2) =
        mkIdent ident <> "Eq " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Lt dst src1 src2) =
        mkIdent ident <> "Lt " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Le dst src1 src2) =
        mkIdent ident <> "Le " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Gt dst src1 src2) =
        mkIdent ident <> "Gt " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Ge dst src1 src2) =
        mkIdent ident <> "Ge " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (Declare var) =
        mkIdent ident <> "Declare " <> showCL 0 var
    showCL ident (SetLabel label) =
        showCL (ident - 1) label <> ":"
    showCL ident (BrTrue var label) =
        mkIdent ident <> "BrTrue " <> showCL 0 var <> " " <> showCL 0 label
    showCL ident (BrFalse var label) =
        mkIdent ident <> "BrFalse " <> showCL 0 var <> " " <> showCL 0 label
    showCL ident (BrAlways label) =
        mkIdent ident <> "BrAlways " <> showCL 0 label
    showCL ident (Call dst (CoreFunDecl label _ _) args) =
        mkIdent ident <> "Call " <> showCL 0 dst <> " " <>
            showCL 0 label <> " " <> showCL 0 args
    showCL ident (CallV dst src args) =
        mkIdent ident <> "CallV " <> showCL 0 dst <> " " <>
            showCL 0 src <> " " <> showCL 0 args
    showCL ident (StoreI dst i) =
        mkIdent ident <> "StoreI " <> showCL 0 dst <> " " <> showCL 0 i
    showCL ident (StoreC dst c) =
        mkIdent ident <> "StoreC " <> showCL 0 dst <> " " <> showCL 0 c
    showCL ident (StoreB dst b) =
        mkIdent ident <> "StoreB " <> showCL 0 dst <> " " <> showCL 0 b
    showCL ident (StoreV dst src) =
        mkIdent ident <> "StoreV " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (StoreA dst src) =
        mkIdent ident <> "StoreA " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (StoreL dst (CoreFunDecl label _ _)) =
        mkIdent ident <> "StoreL " <> showCL 0 dst <> " " <> label
    showCL ident (StoreVUnsafe dst src) =
        mkIdent ident <> "StoreVUnsafe " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (LoadA dst src) =
        mkIdent ident <> "LoadA " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (Ref dst src) =
        mkIdent ident <> "Ref " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (MkNilList dst) =
        mkIdent ident <> "MkNilList " <> showCL 0 dst
    showCL ident (ConsList dst src1 src2) =
        mkIdent ident <> "ConsList " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (MkTup dst src1 src2) =
        mkIdent ident <> "MkTup " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
    showCL ident (RetV src) =
        mkIdent ident <> "RetV " <> showCL 0 src
    showCL ident Halt =
        mkIdent ident <> "Halt"
    showCL ident (PrintI i) =
        mkIdent ident <> "PrintI " <> showCL 0 i
    showCL ident (PrintC c) =
        mkIdent ident <> "PrintC " <> showCL 0 c
