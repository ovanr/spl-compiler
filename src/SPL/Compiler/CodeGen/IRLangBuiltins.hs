{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.CodeGen.IRLangBuiltins where

import Control.Lens hiding (Snoc)

import SPL.Compiler.CodeGen.IRLang
import SPL.Compiler.CodeGen.IRLangGenLib
import SPL.Compiler.Common.TypeFunc

mkBuiltins :: IRMonad (Some1 (HList IRFunDef))
mkBuiltins = do
    case mkMagicFuncs of
        Some1 magicFuncs -> do
            pow <- mkPowFunc
            return $ Some1 (pow :+: magicFuncs)

mkPowFunc :: IRMonad (IRFunDef '[Int, Int, Int])
mkPowFunc = do
        let arg1 = Var "x" IRIntType
            arg2 = Var "y" IRIntType
            funDecl' = IRFunDecl' (IRFunDecl "0pow" (arg1 :+: arg2 :+: HNil) IRIntType)

        funBody <- declareBodyAs $ do
            returnFalse <- mkLabel "ReturnFalse"
            end <- mkLabel "End"
            whileStart <- mkLabel "WhileStart"

            result <- mkTmpVar IRIntType
            body <>= [StoreI result 1]
            tmp1 <- mkTmpVar IRBoolType
            one <- mkTmpVar IRIntType
            body <>= [StoreI one 1]

            body <>= [SetLabel whileStart]

            body <>= [Lt tmp1 arg2 one , BrTrue tmp1 end]

            body <>= [Mul result result result]
            body <>= [Sub arg2 arg2 one]
            body <>= [ BrAlways whileStart ]

            body <>= [SetLabel end]
            body <>= [RetV result]

        return (IRFunDef funDecl' funBody)

mkMagicFuncs :: Some1 (HList IRFunDef)
mkMagicFuncs = Some1 $ isEmpty :+: hd :+: tl :+: fst :+: snd :+: hdAssign 
                               :+: tlAssign :+: fstAssign :+: sndAssign :+: HNil
    where
        mkMagicFun :: Identifier -> HList Var xs -> IRType r -> IRFunDef (Snoc xs r)
        mkMagicFun id args retType = IRFunDef (IRFunDecl' (IRFunDecl id args retType)) [Halt]

        isEmpty :: IRFunDef '[Ptr [Unknown], Bool]
        isEmpty = mkMagicFun "isEmpty" (Var "x" (IRListType (IRUnknownType "a")) :+: HNil) IRBoolType

        hd :: IRFunDef '[Ptr [Unknown], Unknown]
        hd = mkMagicFun "hd" (Var "x" (IRListType (IRUnknownType "a")) :+: HNil) (IRUnknownType "a")

        tl :: IRFunDef '[Ptr [Unknown], Ptr [Unknown]]
        tl = mkMagicFun "tl" (Var "x" (IRListType (IRUnknownType "a")) :+: HNil) (IRListType (IRUnknownType "a"))

        fst :: IRFunDef '[Ptr (Unknown, Unknown), Unknown]
        fst = mkMagicFun "fst" (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) :+: HNil) (IRUnknownType "a")

        snd :: IRFunDef '[Ptr (Unknown, Unknown), Unknown]
        snd = mkMagicFun "snd" (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) :+: HNil) (IRUnknownType "b")

        hdAssign :: IRFunDef '[Ptr [Unknown], Ptr Unknown]
        hdAssign = mkMagicFun "0hd_assign"
                        (Var "x" (IRListType (IRUnknownType "a")) :+: HNil)
                        (IRPtrType (IRUnknownType "a"))

        tlAssign :: IRFunDef '[Ptr [Unknown], Ptr (Ptr [Unknown])]
        tlAssign = mkMagicFun "0tl_assign"
                        (Var "x" (IRListType (IRUnknownType "a")) :+: HNil)
                        (IRPtrType $ IRListType (IRUnknownType "a"))

        fstAssign :: IRFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        fstAssign = mkMagicFun "0fst_assign"
                        (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) :+: HNil)
                        (IRPtrType (IRUnknownType "a"))

        sndAssign :: IRFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        sndAssign = mkMagicFun "0snd_assign"
                        (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) :+: HNil)
                        (IRPtrType (IRUnknownType "b"))

