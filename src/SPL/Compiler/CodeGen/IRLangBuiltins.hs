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
        let arg1 = Var "x" IRIntType Declared
            arg2 = Var "y" IRIntType Declared
            funDecl' = IRFunDecl' (IRFunDecl "0pow" (arg1 :+: arg2 :+: HNil) IRIntType)

        funBody <- declareBodyAs $ do
            returnFalse <- mkLabel "ReturnFalse"
            end <- mkLabel "End"
            whileStart <- mkLabel "WhileStart"

            let resultV = Var "acc" IRIntType Declared
            body <>= [DeclareV resultV]
            body <>= [StoreV resultV (IRLit $ IRInt 1)]
            tmp1 <- mkTmpVar IRBoolType

            body <>= [SetLabel whileStart]

            body <>= [Lt tmp1 (IRVar arg2) (IRLit $ IRInt 1), BrTrue (IRVar tmp1) end]

            body <>= [Mul resultV (IRVar resultV) (IRVar arg1)]
            body <>= [Sub arg2 (IRVar arg2) (IRLit $ IRInt 1)]
            body <>= [BrAlways whileStart]

            body <>= [SetLabel end]
            body <>= [Ret (IRVar resultV)]

        return (IRFunDef funDecl' funBody)

mkMagicFuncs :: Some1 (HList IRFunDef)
mkMagicFuncs = Some1 $ isEmpty :+: hd :+: tl :+: fst :+: snd :+: hdAssign 
                               :+: tlAssign :+: fstAssign :+: sndAssign :+: HNil
    where
        mkMagicFun :: Identifier -> HList Var xs -> IRType r -> IRFunDef (Snoc xs r)
        mkMagicFun id args retType = IRFunDef (IRFunDecl' (IRFunDecl id args retType)) [Halt]

        isEmpty :: IRFunDef '[Ptr [Unknown], Bool]
        isEmpty = mkMagicFun "isEmpty" (Var "x" (IRListType (IRUnknownType "a")) Declared :+: HNil) IRBoolType

        hd :: IRFunDef '[Ptr [Unknown], Unknown]
        hd = mkMagicFun "hd" (Var "x" (IRListType (IRUnknownType "a")) Declared :+: HNil) (IRUnknownType "a")

        tl :: IRFunDef '[Ptr [Unknown], Ptr [Unknown]]
        tl = mkMagicFun "tl" (Var "x" (IRListType (IRUnknownType "a")) Declared :+: HNil) (IRListType (IRUnknownType "a"))

        fst :: IRFunDef '[Ptr (Unknown, Unknown), Unknown]
        fst = mkMagicFun "fst" (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) Declared :+: HNil) (IRUnknownType "a")

        snd :: IRFunDef '[Ptr (Unknown, Unknown), Unknown]
        snd = mkMagicFun "snd" (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) Declared :+: HNil) (IRUnknownType "b")

        hdAssign :: IRFunDef '[Ptr [Unknown], Ptr Unknown]
        hdAssign = mkMagicFun "0hd_assign"
                        (Var "x" (IRListType (IRUnknownType "a")) Declared :+: HNil)
                        (IRPtrType (IRUnknownType "a"))

        tlAssign :: IRFunDef '[Ptr [Unknown], Ptr (Ptr [Unknown])]
        tlAssign = mkMagicFun "0tl_assign"
                        (Var "x" (IRListType (IRUnknownType "a")) Declared :+: HNil)
                        (IRPtrType $ IRListType (IRUnknownType "a"))

        fstAssign :: IRFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        fstAssign = mkMagicFun "0fst_assign"
                        (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) Declared :+: HNil)
                        (IRPtrType (IRUnknownType "a"))

        sndAssign :: IRFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        sndAssign = mkMagicFun "0snd_assign"
                        (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) Declared :+: HNil)
                        (IRPtrType (IRUnknownType "b"))

