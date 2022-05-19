{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module SPL.Compiler.CodeGen.IRLangPrinter where

import Data.Text (Text)
import qualified Data.Text as T

import SPL.Compiler.CodeGen.IRLang
import SPL.Compiler.Common.TypeFunc

mkIdent :: Int -> Text
mkIdent n = foldl (<>) "" $ replicate n "   "

class IRLangPrinter a where
    showCL :: Int -> a -> Text

instance IRLangPrinter Int where
    showCL _ i = T.pack (show i)

instance IRLangPrinter Bool where
    showCL _ b = T.pack (show b)

instance IRLangPrinter Char where
    showCL _ c = T.pack (show c)

instance IRLangPrinter Label where
    showCL ident l = mkIdent ident <> l

instance IRLangPrinter (IRType a) where
    showCL _ t = T.pack (show t)

instance IRLangPrinter (Var a) where
    showCL _ (Var id t _) = id <> "%" <> showCL 0 t

instance IRLangPrinter (Value a) where
    showCL _ (IRVar v) = showCL 0 v
    showCL _ (IRLit l) = showCL 0 l

instance IRLangPrinter (IRConstant a) where
    showCL _ IRVoid  = "()"
    showCL _ (IRInt i) = T.pack (show i)
    showCL _ (IRBool b) = T.pack (show b)
    showCL _ (IRChar c) = "'" <> T.singleton c <> "'"
    showCL _ (IRFun (IRFunDecl label _ _)) = label

instance IRLangPrinter (HList Var xs) where
    showCL _ = T.intercalate " " . hListMapToList (showCL 0)

instance IRLangPrinter (HList Value xs) where
    showCL _ = T.intercalate " " . hListMapToList (showCL 0)

instance IRLangPrinter (IRLang gs fs) where 
    showCL ident (IRLang globals funcs) = 
        showCL ident globals <> "\n" <> showCL ident funcs

instance IRLangPrinter (HList IRGlobal gs) where
    showCL ident = T.intercalate "\n" . hListMapToList (showCL 0)

instance IRLangPrinter (IRGlobal a) where
    showCL ident (IRGlobal var) = "GLOBAL " <> showCL ident var

instance IRLangPrinter (HList IRFunDecl' gs) where
    showCL ident = T.intercalate "\n" . hListMapToList (showCL 0)

instance IRLangPrinter (IRFunDef xs) where
    showCL ident (IRFunDef decl body) = 
        showCL ident decl <> "\n" <> showCL (ident + 2) body

instance IRLangPrinter (HList IRFunDef gs) where
    showCL ident = T.intercalate "\n" . hListMapToList (showCL 0)

instance IRLangPrinter (IRFunDecl' xs) where
    showCL ident (IRFunDecl' decl) = showCL ident decl

instance IRLangPrinter (IRFunDecl as r) where
    showCL ident (IRFunDecl label args retType) =
        mkIdent ident <> showCL 0 label <> 
            "(" <> showCL 0 args <> ") %" <> showCL 0 retType <> ":"

instance IRLangPrinter [IRInstr] where
    showCL ident = T.unlines . map (showCL ident)

instance IRLangPrinter IRInstr where
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
    showCL ident (Xor dst src1 src2) =
        mkIdent ident <> "Xor " <> showCL 0 dst <> " " <> showCL 0 src1 <> " " <> showCL 0 src2
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
    showCL ident (DeclareV var) =
        mkIdent ident <> "DeclareV " <> showCL 0 var
    showCL ident (DeclareTmp var) =
        mkIdent ident <> "DeclareTmp " <> showCL 0 var
    showCL ident (SetLabel label) =
        showCL (ident - 1) label <> ":"
    showCL ident (BrTrue var label) =
        mkIdent ident <> "BrTrue " <> showCL 0 var <> " " <> showCL 0 label
    showCL ident (BrFalse var label) =
        mkIdent ident <> "BrFalse " <> showCL 0 var <> " " <> showCL 0 label
    showCL ident (BrAlways label) =
        mkIdent ident <> "BrAlways " <> showCL 0 label
    showCL ident (Call dst src args) =
        mkIdent ident <> "Call " <> showCL 0 dst <> " " <>
            showCL 0 src <> " " <> showCL 0 args
    showCL ident (StoreV dst src) =
        mkIdent ident <> "StoreV " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (StoreA dst src) =
        mkIdent ident <> "StoreA " <> showCL 0 dst <> " " <> showCL 0 src
    showCL ident (Cast dst src) =
        mkIdent ident <> "Cast " <> showCL 0 dst <> " " <> showCL 0 src
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
    showCL ident (Ret src) =
        mkIdent ident <> "Ret " <> showCL 0 src
    showCL ident Halt =
        mkIdent ident <> "Halt"
    showCL ident (PrintI i) =
        mkIdent ident <> "PrintI " <> showCL 0 i
    showCL ident (PrintC c) =
        mkIdent ident <> "PrintC " <> showCL 0 c
