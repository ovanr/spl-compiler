{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.CodeGen.IRLangTConGen where

import qualified Data.Text as T
import Control.Lens
import Control.Monad
import GHC.Stack

import SPL.Compiler.CodeGen.IRLang
import SPL.Compiler.CodeGen.IRLangGenLib
import SPL.Compiler.Common.TypeFunc

class GenTConFun a where
    genEqIRInstr :: Var a -> Var a -> IRMonad (Var Bool)
    genEqIRInstr arg1 arg2 = genEqOrdIRInstr genEqIRInstr arg1 arg2
    genOrdIRInstr :: Var a -> Var a -> IRMonad (Var Bool)
    genOrdIRInstr arg1 arg2 = genEqOrdIRInstr genOrdIRInstr arg1 arg2
    genEqOrdIRInstr :: (forall a. GenTConFun a => Var a -> Var a -> IRMonad (Var Bool)) -> 
                         Var a -> Var a -> IRMonad (Var Bool)
    genPrintIRInstr :: Var a -> IRMonad ()

instance GenTConFun Unit where
    genEqIRInstr arg1 arg2 = do
        dst <- mkTmpVar IRBoolType
        body <>= [StoreB dst True]
        return dst
    genOrdIRInstr = genEqIRInstr
    genEqOrdIRInstr f = f
    genPrintIRInstr _ = do
        tmp <- mkTmpVar IRCharType
        body <>= [StoreC tmp 'V', PrintC tmp]

instance GenTConFun Int where
    genEqIRInstr arg1 arg2 = do
        dst <- mkTmpVar IRBoolType
        body <>= [Eq dst arg1 arg2]
        return dst
    genOrdIRInstr arg1 arg2 = do
        dst <- mkTmpVar IRBoolType
        body <>= [Lt dst arg1 arg2]
        return dst
    genEqOrdIRInstr f = f
    genPrintIRInstr arg1 =
        body <>= [PrintI arg1]

instance GenTConFun Bool where
    genEqIRInstr arg1 arg2 = do
        src1 <- mkTmpVar IRIntType
        src2 <- mkTmpVar IRIntType
        dst  <- mkTmpVar IRBoolType
        body <>= [StoreVUnsafe src1 arg1,
                  StoreVUnsafe src2 arg2,
                  Eq dst src1 src2]
        return dst
    genOrdIRInstr = genEqIRInstr
    genEqOrdIRInstr f = f
    genPrintIRInstr arg1 = do
        printFalse <- mkLabel "PrintFalse"
        end <- mkLabel "End"
        tmp <- mkTmpVar IRCharType
        body <>= [BrFalse arg1 printFalse]
        body <>= [StoreC tmp 'T',
                  PrintC tmp,
                  StoreC tmp 'r',
                  PrintC tmp,
                  StoreC tmp 'u',
                  PrintC tmp,
                  StoreC tmp 'e',
                  PrintC tmp,
                  BrAlways end]
        body <>= [SetLabel printFalse]
        body <>= [StoreC tmp 'F',
                  PrintC tmp,
                  StoreC tmp 'a',
                  PrintC tmp,
                  StoreC tmp 'l',
                  PrintC tmp,
                  StoreC tmp 's',
                  PrintC tmp,
                  StoreC tmp 'e',
                  PrintC tmp]
        body <>= [SetLabel end]

instance GenTConFun Char where
    genEqIRInstr arg1 arg2 = do
        src1 <- mkTmpVar IRIntType
        src2 <- mkTmpVar IRIntType
        dst  <- mkTmpVar IRBoolType
        body <>= [StoreVUnsafe src1 arg1,
                  StoreVUnsafe src2 arg2,
                  Eq dst src1 src2]
        return dst
    genOrdIRInstr arg1 arg2 = do
        src1 <- mkTmpVar IRIntType
        src2 <- mkTmpVar IRIntType
        dst  <- mkTmpVar IRBoolType
        body <>= [StoreVUnsafe src1 arg1,
                  StoreVUnsafe src2 arg2,
                  Lt dst src1 src2]
        return dst
    genEqOrdIRInstr _ _ _ = coreError
    genPrintIRInstr arg1 =
        body <>= [PrintC arg1]


instance GenTConFun a => GenTConFun (Ptr [a]) where
    -- Given arguments: arg1 arg2
    -- while (True) {
    --     if (isEmpty(arg1) && isEmpty(arg2))
    --         return True;
    --     if (!isEmpty(arg1) && isEmpty(arg2))
    --         return False;
    --     if (isEmpty(arg1) && !isEmpty(arg2))
    --         return False;

    --     hd1 = hd(arg1);
    --     hd2 = hd(arg2);
    --     if (hd1 != hd2)
    --         return False;
    --     arg1 = tl(arg1);
    --     arg2 = tl(arg2);
    -- }
    genEqOrdIRInstr f arg1@(Var _ listT@(IRListType elemT)) arg2 = do
        returnFalse <- mkLabel "ReturnFalse"
        end <- mkLabel "End"
        whileStart <- mkLabel "WhileStart"

        result <- mkTmpVar IRBoolType
        body <>= [StoreB result True]
        tmp1 <- mkTmpVar IRBoolType
        tmp2 <- mkTmpVar IRBoolType
        body <>= [SetLabel whileStart]

        Some1 isEmpty1@(Var _ IRBoolType) <- callFunWith "isEmpty" [Some1 arg1]
        Some1 isEmpty2@(Var _ IRBoolType) <- callFunWith "isEmpty" [Some1 arg2]

        body <>= [And tmp1 isEmpty1 isEmpty2, BrTrue tmp1 end]
        body <>= [Not tmp2 isEmpty1, And tmp1 tmp2 isEmpty2, BrTrue tmp1 returnFalse]
        body <>= [Not tmp2 isEmpty2, And tmp1 isEmpty1 tmp2, BrTrue tmp1 returnFalse]

        Some1 hd1 <- callFunWith "hd" [Some1 arg1]
        hd1' <- unsafeCast hd1 elemT
        Some1 hd2 <- callFunWith "hd" [Some1 arg2]
        hd2' <- unsafeCast hd2 elemT

        hdEqual <- f hd1' hd2'
        body <>= [ BrFalse hdEqual returnFalse ]

        Some1 tl1 <- callFunWith "tl" [Some1 arg1]
        tl1' <- unsafeCast tl1 listT
        Some1 tl2 <- callFunWith "tl" [Some1 arg2]
        tl2' <- unsafeCast tl1 listT

        body <>= [StoreV arg1 tl1', StoreV arg2 tl2', BrAlways whileStart]
        body <>= [SetLabel returnFalse, StoreB result False]
        body <>= [SetLabel end]

        return result
    genEqOrdIRInstr _ _ _ = coreError
    genPrintIRInstr arg@(Var _ listT@(IRListType elemT)) = do
        whileStart <- mkLabel "WhileStart"
        end <- mkLabel "End"

        tmp1 <- mkTmpVar IRBoolType
        tmp2 <- mkTmpVar IRCharType

        body <>= [StoreC tmp2 '[', PrintC tmp2]
        body <>= [SetLabel whileStart]

        Some1 isEmpty@(Var _ IRBoolType) <- callFunWith "isEmpty" [Some1 arg]

        body <>= [BrTrue isEmpty end]

        Some1 hd <- callFunWith "hd" [Some1 arg]
        hd' <- unsafeCast hd elemT

        genPrintIRInstr hd'

        Some1 tl <- callFunWith "tl" [Some1 arg]

        Some1 isEmpty@(Var _ IRBoolType) <- callFunWith "isEmpty" [Some1 tl]
        body <>= [BrTrue isEmpty end]
        body <>= [StoreC tmp2 ' ', PrintC tmp2]

        tl' <- unsafeCast tl listT
        body <>= [StoreV arg tl', BrAlways whileStart]
        body <>= [SetLabel end]
        body <>= [StoreC tmp2 ']', PrintC tmp2]
    genPrintIRInstr _ = coreError

instance (GenTConFun a, GenTConFun b) => GenTConFun (Ptr (a,b)) where
    genEqOrdIRInstr f arg1@(Var _ tupT@(IRTupleType elemT1 elemT2)) arg2 = do
        returnFalse <- mkLabel "ReturnFalse"
        end <- mkLabel "End"

        result <- mkTmpVar IRBoolType
        body <>= [StoreB result True]

        Some1 fst1 <- callFunWith "fst" [Some1 arg1]
        fst1' <- unsafeCast fst1 elemT1
        Some1 fst2 <- callFunWith "fst" [Some1 arg2]
        fst2' <- unsafeCast fst2 elemT1

        fstEqual <- f fst1' fst2'
        body <>= [BrFalse fstEqual returnFalse]

        Some1 snd1 <- callFunWith "snd" [Some1 arg1]
        snd1' <- unsafeCast snd1 elemT2
        Some1 snd2 <- callFunWith "snd" [Some1 arg2]
        snd2' <- unsafeCast snd2 elemT2

        sndEqual <- genEqIRInstr snd1' snd2'
        body <>= [BrFalse sndEqual returnFalse]
        body <>= [BrAlways end]

        body <>= [SetLabel returnFalse, StoreB result False, BrAlways end]
        body <>= [SetLabel end]

        return result
    genEqOrdIRInstr _ _ _ = coreError
    genPrintIRInstr arg@(Var _ (IRTupleType elemT1 elemT2)) = do
        tmp <- mkTmpVar IRCharType

        body <>= [StoreC tmp '(', PrintC tmp]

        Some1 fst <- callFunWith "fst" [Some1 arg]
        fst' <- unsafeCast fst elemT1
        genPrintIRInstr fst'

        body <>= [StoreC tmp ',', PrintC tmp]

        Some1 snd <- callFunWith "snd" [Some1 arg]
        snd' <- unsafeCast snd elemT2
        genPrintIRInstr snd'

        body <>= [StoreC tmp ')', PrintC tmp]
    genPrintIRInstr _ = coreError

toConstrained :: (MonadFail m, HasCallStack) => IRType a -> m (Constrained GenTConFun IRType a)
toConstrained IRIntType = pure (Constrained IRIntType)
toConstrained IRBoolType = pure (Constrained IRBoolType)
toConstrained IRCharType = pure (Constrained IRCharType)
toConstrained IRVoidType = pure (Constrained IRVoidType)
toConstrained (IRListType elemT) = do
    Constrained elemT' <- toConstrained elemT
    pure . Constrained $ IRListType elemT'
toConstrained (IRTupleType elemT1 elemT2) = do
    Constrained elemT1' <- toConstrained elemT1
    Constrained elemT2' <- toConstrained elemT2
    pure . Constrained $ IRTupleType elemT1' elemT2'
toConstrained t = fail $
    "Cannot generate overloaded constraint for this type: " <> show t

solveFunDeclConstraints :: IRFunDecl xs r -> IRMonad [Some1 IRFunDef]
solveFunDeclConstraints (IRFunDecl _ args _) = do
    forM (hListToList args) $ \(Some1 (Var id (IRFunType (varT :+: _) _))) -> do
        Constrained varT' <- toConstrained varT
        body .= []
        case T.unpack id of
            ('0':'e':'q':'_':'c':'o':'n':_) -> do
                funName <- mkLabel "eq_con"
                let arg1 = Var "x" varT
                    arg2 = Var "y" varT
                    funDecl' = IRFunDecl' (IRFunDecl funName (arg1 :+: arg2 :+: HNil) IRBoolType)
                funBody <- declareBodyAs $ do
                    dst <- genEqIRInstr arg1 arg2
                    body <>= [RetV dst]
                return . Some1 $ IRFunDef funDecl' funBody
            ('0':'o':'r':'d':'_':'c':'o':'n':_) -> do
                funName <- mkLabel "ord_con"
                let arg1 = Var "x" varT
                    arg2 = Var "y" varT
                    funDecl' = IRFunDecl' (IRFunDecl funName (arg1 :+: arg2 :+: HNil) IRBoolType)
                funBody <- declareBodyAs $ do
                    dst <- genOrdIRInstr arg1 arg2
                    body <>= [RetV dst]
                return . Some1 $ IRFunDef funDecl' funBody
            ('0':'p':'r':'i':'n':'t':'_':'c':'o':'n':_) -> do
                funName <- mkLabel "print_con"
                let arg = Var "x" varT
                    funDecl' = IRFunDecl' (IRFunDecl funName (arg :+: HNil) IRVoidType)
                funBody <- declareBodyAs $ do
                    genPrintIRInstr arg
                    dst <- mkTmpVar IRVoidType
                    body <>= [RetV dst]
                return . Some1 $ IRFunDef funDecl' funBody
            _ -> coreError
