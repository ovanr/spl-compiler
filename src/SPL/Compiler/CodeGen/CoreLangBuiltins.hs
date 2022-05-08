{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.CodeGen.CoreLangBuiltins where

import Control.Lens hiding (Snoc)

import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.CodeGen.CoreLangGenLib
import SPL.Compiler.Common.TypeFunc

mkBuiltins :: CoreMonad (Some1 (HList CoreFunDef))
mkBuiltins = do
    case mkMagicFuncs of
        Some1 magicFuncs -> do
            pow <- mkPowFunc
            return $ Some1 (pow :+: magicFuncs)

mkPowFunc :: CoreMonad (CoreFunDef '[Int, Int, Int])
mkPowFunc = do
        let arg1 = Var "x" CoreIntType
            arg2 = Var "y" CoreIntType
            funDecl' = CoreFunDecl' (CoreFunDecl "'pow" (arg1 :+: arg2 :+: HNil) CoreIntType)

        funBody <- declareBodyAs $ do
            returnFalse <- mkLabel "ReturnFalse"
            end <- mkLabel "End"
            whileStart <- mkLabel "WhileStart"

            result <- mkTmpVar CoreIntType
            body <>= [StoreI result 1]
            tmp1 <- mkTmpVar CoreBoolType
            one <- mkTmpVar CoreIntType
            body <>= [StoreI one 1]

            body <>= [SetLabel whileStart]

            body <>= [Lt tmp1 arg2 one , BrTrue tmp1 end]

            body <>= [Mul result result result]
            body <>= [Sub arg2 arg2 one]
            body <>= [ BrAlways whileStart ]

            body <>= [SetLabel end]
            body <>= [RetV result]

        return (CoreFunDef funDecl' funBody)

mkMagicFuncs :: Some1 (HList CoreFunDef)
mkMagicFuncs = Some1 $ isEmpty :+: hd :+: tl :+: fst :+: snd :+: hdAssign 
                               :+: tlAssign :+: fstAssign :+: sndAssign :+: HNil
    where
        mkMagicFun :: Identifier -> HList Var xs -> CoreType r -> CoreFunDef (Snoc xs r)
        mkMagicFun id args retType = CoreFunDef (CoreFunDecl' (CoreFunDecl id args retType)) [Halt]

        isEmpty :: CoreFunDef '[Ptr [Unknown], Bool]
        isEmpty = mkMagicFun "isEmpty" (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil) CoreBoolType

        hd :: CoreFunDef '[Ptr [Unknown], Unknown]
        hd = mkMagicFun "hd" (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil) (CoreUnknownType "a")

        tl :: CoreFunDef '[Ptr [Unknown], Ptr [Unknown]]
        tl = mkMagicFun "tl" (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil) (CoreListType (CoreUnknownType "a"))

        fst :: CoreFunDef '[Ptr (Unknown, Unknown), Unknown]
        fst = mkMagicFun "fst" (Var "x" (CoreTupleType (CoreUnknownType "a") (CoreUnknownType "b")) :+: HNil) (CoreUnknownType "a")

        snd :: CoreFunDef '[Ptr (Unknown, Unknown), Unknown]
        snd = mkMagicFun "snd" (Var "x" (CoreTupleType (CoreUnknownType "a") (CoreUnknownType "b")) :+: HNil) (CoreUnknownType "b")

        hdAssign :: CoreFunDef '[Ptr [Unknown], Ptr Unknown]
        hdAssign = mkMagicFun "'hd_assign"
                        (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil)
                        (CorePtrType (CoreUnknownType "a"))

        tlAssign :: CoreFunDef '[Ptr [Unknown], Ptr (Ptr [Unknown])]
        tlAssign = mkMagicFun "'tl_assign"
                        (Var "x" (CoreListType (CoreUnknownType "a")) :+: HNil)
                        (CorePtrType $ CoreListType (CoreUnknownType "a"))

        fstAssign :: CoreFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        fstAssign = mkMagicFun "'fst_assign"
                        (Var "x" (CoreTupleType (CoreUnknownType "a") (CoreUnknownType "b")) :+: HNil)
                        (CorePtrType (CoreUnknownType "a"))

        sndAssign :: CoreFunDef '[Ptr (Unknown, Unknown), Ptr Unknown]
        sndAssign = mkMagicFun "'snd_assign"
                        (Var "x" (CoreTupleType (CoreUnknownType "a") (CoreUnknownType "b")) :+: HNil)
                        (CorePtrType (CoreUnknownType "b"))

