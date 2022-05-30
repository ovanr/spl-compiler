{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

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
        let arg1 = Var "x" IRIntType Local
            arg2 = Var "y" IRIntType Local
            funDecl' = IRFunDecl' (IRFunDecl "_pow" (arg1 :+: arg2 :+: HNil) IRIntType)

        funBody <- declareBodyAs $ do
            returnFalse <- mkLabel "ReturnFalse"
            end <- mkLabel "End"
            whileStart <- mkLabel "WhileStart"

            let resultV = Var "acc" IRIntType Local
            let tmp1 = Var "tmp" IRBoolType Local
            body <>= [DeclareV resultV, DeclareV tmp1]
            body <>= [StoreV resultV (IRLit $ IRInt 1)]

            body <>= [SetLabel whileStart]

            body <>= [Lt tmp1 (IRVar arg2) (IRLit $ IRInt 1), BrTrue (IRVar tmp1) end]

            body <>= [Mul resultV (IRVar resultV) (IRVar arg1)]
            body <>= [Sub arg2 (IRVar arg2) (IRLit $ IRInt 1)]
            body <>= [BrAlways whileStart]

            body <>= [SetLabel end]
            body <>= [Ret (IRVar resultV)]

        return (IRFunDef funDecl' funBody)

mkMagicFuncs :: Some1 (HList IRFunDef)
mkMagicFuncs = Some1 $ print :+: isEmpty :+: hd :+: tl :+: fst :+: snd :+: 
                       hdAssign :+: tlAssign :+: fstAssign :+: sndAssign :+: HNil
    where
        mkMagicFun :: Identifier -> HList Var xs -> IRType r -> IRFunDef (Snoc xs r)
        mkMagicFun id args retType = IRFunDef (IRFunDecl' (IRFunDecl id args retType)) [Halt]

        print :: IRFunDef '[Ptr ('[Unknown] --> Unit), Unknown, Unit]
        print = mkMagicFun "print" (Var "p" (IRFunType (IRUnknownType "a" :+: HNil) IRVoidType) Local :+:
                                    Var "x" (IRUnknownType "a") Local :+: 
                                    HNil) IRVoidType

        isEmpty :: IRFunDef '[Ptr [Unknown], Bool]
        isEmpty = mkMagicFun "isEmpty" (Var "x" (IRListType (IRUnknownType "a")) Local :+: HNil) IRBoolType

        hd :: IRFunDef '[Ptr [Unknown], Unknown]
        hd = mkMagicFun "hd" 
                (Var "x" (IRListType (IRUnknownType "a")) Local :+: HNil) 
                (IRUnknownType "a")

        tl :: IRFunDef '[Ptr [Unknown], Ptr [Unknown]]
        tl = mkMagicFun "tl" 
                (Var "x" (IRListType (IRUnknownType "a")) Local :+: HNil) 
                (IRListType (IRUnknownType "a"))

        fst :: IRFunDef '[Ptr (Unknown, Unknown), Unknown]
        fst = mkMagicFun "fst" 
                (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) Local :+: HNil) 
                (IRUnknownType "a")

        snd :: IRFunDef '[Ptr (Unknown, Unknown), Unknown]
        snd = mkMagicFun "snd" 
                    (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) Local :+: HNil) 
                    (IRUnknownType "b")

        hdAssign :: IRFunDef '[Ptr [Unknown], Ptr Unknown]
        hdAssign = mkMagicFun "_hd_assign"
                        (Var "x" (IRListType (IRUnknownType "a")) Local :+: HNil)
                        (IRPtrType (IRUnknownType "a"))

        tlAssign :: IRFunDef '[Ptr [Unknown], Ptr (Ptr [Unknown])]
        tlAssign = mkMagicFun "_tl_assign"
                        (Var "x" (IRListType (IRUnknownType "a")) Local :+: HNil)
                        (IRPtrType $ IRListType (IRUnknownType "a"))

        fstAssign :: IRFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        fstAssign = mkMagicFun "_fst_assign"
                        (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) Local :+: HNil)
                        (IRPtrType (IRUnknownType "a"))

        sndAssign :: IRFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        sndAssign = mkMagicFun "_snd_assign"
                        (Var "x" (IRTupleType (IRUnknownType "a") (IRUnknownType "b")) Local :+: HNil)
                        (IRPtrType (IRUnknownType "b"))

