{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}

module SPL.Compiler.CodeGen.TestCoreLangGen (htf_thisModulesTests) where

import Test.Framework 
import Data.Text (Text)
import Data.Proxy

import SPL.Compiler.CodeGen.CoreLangGen
import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.Common.TypeFunc
import qualified SPL.Compiler.SemanticAnalysis.TCT as TCT
import SPL.Compiler.SemanticAnalysis.Testable

list1 (id, t) = (Var id t) :+: HNil
list2 (id, t) v2 = (Var id t) :+: list1 v2
list3 (id, t) v2 v3 = (Var id t) :+: list2 v2 v3
list4 (id, t) v2 v3 v4 = (Var id t) :+: list3 v2 v3 v4

-- testExprToCoreInstr :: TCT.TCTExpr -> CoreMonad (Some1 Var, [CoreInstr])

-- executeCodeGenTests :: [TypeCheckTestEnv a] ->
--                   (HList CoreFunDecl' xs -> a -> CoreMonad (Some1 Var, [CoreInstr])) ->
--                   IO ()
