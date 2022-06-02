{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
module SPL.Compiler.CodeGen.IRLangTConGen where

import SPL.Compiler.CodeGen.IRLang

printString :: String -> [IRInstr]

mkEqOrdFunDecl :: Identifier -> IRType a -> IRFunDecl '[a, a] Bool

mkEqFunDecl :: IRType a -> IRFunDecl '[a, a] Bool

mkOrdFunDecl :: IRType a -> IRFunDecl '[a, a] Bool

mkPrintFunDecl :: IRType a -> IRFunDecl '[a] Unit

mkEqFunName :: IRType a -> Identifier

mkOrdFunName :: IRType a -> Identifier

mkPrintFunName :: IRType a -> Identifier

textifyType :: IRType a -> Identifier
