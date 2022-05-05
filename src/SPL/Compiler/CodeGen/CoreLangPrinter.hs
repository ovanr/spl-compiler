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
    showCL _ l = l

instance CoreLangPrinter (CoreType a) where
    showCL _ t = T.pack (show t)

instance CoreLangPrinter (Var a) where
    showCL _ (Var id t) = id <> showCL 0 t

instance CoreLangPrinter (HList Var xs) where
    showCL _ HNil = ""
    showCL _ (var :+: vars) = showCL 0 var <> " " <> showCL 0 vars

instance CoreLangPrinter (CoreLang gs fs) where 
    showCL ident (CoreLang globals funcs) = 
        showCL ident globals <> "\n" <> showCL ident funcs

instance CoreLangPrinter (HList CoreGlobal gs) where
    showCL ident HNil = ""
    showCL ident (g :+: gs) = showCL ident g <> "\n" <> showCL ident gs

instance CoreLangPrinter (CoreGlobal a) where
    showCL ident (CoreGlobal _ init) = showCL ident init

instance CoreLangPrinter (HList CoreFunDecl' gs) where
    showCL ident HNil = ""
    showCL ident (f :+:fs) = showCL ident f <> "\n" <> showCL ident fs

instance CoreLangPrinter (CoreFunDef xs) where
    showCL ident (CoreFunDef decl body) = 
        showCL ident decl <> "\n" <> showCL ident body

instance CoreLangPrinter (HList CoreFunDef gs) where
    showCL ident HNil = ""
    showCL ident (f :+: fs) = showCL ident f <> "\n" <> showCL ident fs

instance CoreLangPrinter (CoreFunDecl' xs) where
    showCL ident (CoreFunDecl' decl) = showCL ident decl

instance CoreLangPrinter (CoreFunDecl as vs r) where
    showCL ident (CoreFunDecl label args vars retType) =
        mkIdent ident <> showCL 0 label <> 
            "(" <> showCL 0 args <> ") " <> showCL 0 retType <> 
            " [" <> showCL 0 vars <> "]" 

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
    showCL ident (Declare var) =
        mkIdent ident <> "Declare " <> showCL 0 var
    showCL ident (SetLabel label) =
        showCL 0 label <> ":"
    showCL ident (BrTrue var label) =
        mkIdent ident <> "BrTrue " <> showCL 0 var <> " " <> showCL 0 label
    showCL ident (BrFalse var label) =
        mkIdent ident <> "BrFalse " <> showCL 0 var <> " " <> showCL 0 label
    showCL ident (BrAlways label) =
        mkIdent ident <> "BrAlways " <> showCL 0 label
    showCL ident (Call dst (CoreFunDecl label _ _ _) args) =
        mkIdent ident <> "Call " <> showCL 0 dst <> " " <>
            showCL 0 label <> " " <> showCL 0 args
    showCL ident (StoreI dst i) =
        mkIdent ident <> "StoreI " <> showCL 0 dst <> " " <> showCL 0 i
    showCL ident (StoreC dst c) =
        mkIdent ident <> "StoreC " <> showCL 0 dst <> " " <> showCL 0 c
    showCL ident (StoreB dst b) =
        mkIdent ident <> "StoreB " <> showCL 0 dst <> " " <> showCL 0 b
    showCL ident (StoreV dst src) =
        mkIdent ident <> "StoreB " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (StoreA dst src) =
        mkIdent ident <> "StoreB " <> showCL 0 dst <> " " <> showCL 0 src
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
