{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.CodeGen.CoreLangTConGen where

import qualified Data.Text as T
import Control.Lens
import Control.Monad
import GHC.Stack

import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.CodeGen.CoreLangGenLib
import SPL.Compiler.Common.TypeFunc

class GenTConFun a where
    genEqCoreInstr :: Var a -> Var a -> CoreMonad (Var Bool)
    genOrdCoreInstr :: Var a -> Var a -> CoreMonad (Var Bool)
    genEqOrdCoreInstr ::
        (forall a. GenTConFun a => Var a -> Var a -> CoreMonad (Var Bool)) -> Var a -> Var a -> CoreMonad (Var Bool)
    genPrintCoreInstr :: Var a -> CoreMonad ()

instance GenTConFun Unit where
    genEqCoreInstr arg1 arg2 = do
        dst <- mkTmpVar CoreBoolType
        body <>= [StoreB dst True]
        return dst
    genOrdCoreInstr = genEqCoreInstr
    genEqOrdCoreInstr f = f
    genPrintCoreInstr _ = do
        tmp <- mkTmpVar CoreCharType
        body <>= [StoreC tmp 'V', PrintC tmp]

instance GenTConFun Int where
    genEqCoreInstr arg1 arg2 = do
        dst <- mkTmpVar CoreBoolType
        body <>= [Eq dst arg1 arg2]
        return dst
    genOrdCoreInstr arg1 arg2 = do
        dst <- mkTmpVar CoreBoolType
        body <>= [Lt dst arg1 arg2]
        return dst
    genEqOrdCoreInstr f = f
    genPrintCoreInstr arg1 =
        body <>= [PrintI arg1]

instance GenTConFun Bool where
    genEqCoreInstr arg1 arg2 = do
        src1 <- mkTmpVar CoreIntType
        src2 <- mkTmpVar CoreIntType
        dst  <- mkTmpVar CoreBoolType
        body <>= [StoreVUnsafe src1 arg1,
                  StoreVUnsafe src2 arg2,
                  Eq dst src1 src2]
        return dst
    genOrdCoreInstr = genEqCoreInstr
    genEqOrdCoreInstr f = f
    genPrintCoreInstr arg1 = do
        printFalse <- mkLabel "PrintFalse"
        end <- mkLabel "End"
        tmp <- mkTmpVar CoreCharType
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
    genEqCoreInstr arg1 arg2 = do
        src1 <- mkTmpVar CoreIntType
        src2 <- mkTmpVar CoreIntType
        dst  <- mkTmpVar CoreBoolType
        body <>= [StoreVUnsafe src1 arg1,
                  StoreVUnsafe src2 arg2,
                  Eq dst src1 src2]
        return dst
    genOrdCoreInstr arg1 arg2 = do
        src1 <- mkTmpVar CoreIntType
        src2 <- mkTmpVar CoreIntType
        dst  <- mkTmpVar CoreBoolType
        body <>= [StoreVUnsafe src1 arg1,
                  StoreVUnsafe src2 arg2,
                  Lt dst src1 src2]
        return dst
    genEqOrdCoreInstr _ _ _ = coreError
    genPrintCoreInstr arg1 =
        body <>= [PrintC arg1]


instance GenTConFun a => GenTConFun (Ptr [a]) where
    genEqCoreInstr arg1 arg2 = genEqOrdCoreInstr genEqCoreInstr arg1 arg2
    genOrdCoreInstr arg1 arg2 = genEqOrdCoreInstr genOrdCoreInstr arg1 arg2
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
    genEqOrdCoreInstr f arg1@(Var _ listT@(CoreListType elemT)) arg2 = do
        returnFalse <- mkLabel "ReturnFalse"
        end <- mkLabel "End"
        whileStart <- mkLabel "WhileStart"

        result <- mkTmpVar CoreBoolType
        body <>= [StoreB result True]
        tmp1 <- mkTmpVar CoreBoolType
        tmp2 <- mkTmpVar CoreBoolType
        body <>= [SetLabel whileStart]

        Some1 isEmpty1@(Var _ CoreBoolType) <- callFunWith "isEmpty" [Some1 arg1]
        Some1 isEmpty2@(Var _ CoreBoolType) <- callFunWith "isEmpty" [Some1 arg2]

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
    genEqOrdCoreInstr _ _ _ = coreError
    genPrintCoreInstr arg@(Var _ listT@(CoreListType elemT)) = do
        whileStart <- mkLabel "WhileStart"
        end <- mkLabel "End"

        tmp1 <- mkTmpVar CoreBoolType
        body <>= [SetLabel whileStart]

        Some1 isEmpty@(Var _ CoreBoolType) <- callFunWith "isEmpty" [Some1 arg]

        body <>= [BrTrue isEmpty end]

        Some1 hd <- callFunWith "hd" [Some1 arg]
        hd' <- unsafeCast hd elemT

        genPrintCoreInstr hd'

        Some1 tl <- callFunWith "tl" [Some1 arg]
        tl' <- unsafeCast tl listT
        body <>= [StoreV arg tl', BrAlways whileStart]
        body <>= [SetLabel end]
    genPrintCoreInstr _ = coreError

instance (GenTConFun a, GenTConFun b) => GenTConFun (Ptr (a,b)) where
    genEqCoreInstr arg1 arg2 = genEqOrdCoreInstr genEqCoreInstr arg1 arg2
    genOrdCoreInstr arg1 arg2 = genEqOrdCoreInstr genOrdCoreInstr arg1 arg2
    genEqOrdCoreInstr f arg1@(Var _ tupT@(CoreTupleType elemT1 elemT2)) arg2 = do
        returnFalse <- mkLabel "ReturnFalse"
        end <- mkLabel "End"

        result <- mkTmpVar CoreBoolType
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

        sndEqual <- genEqCoreInstr snd1' snd2'
        body <>= [BrFalse sndEqual returnFalse]
        body <>= [BrAlways end]

        body <>= [SetLabel returnFalse, StoreB result False, BrAlways end]
        body <>= [SetLabel end]

        return result
    genEqOrdCoreInstr _ _ _ = coreError
    genPrintCoreInstr arg@(Var _ (CoreTupleType elemT1 elemT2)) = do
        tmp <- mkTmpVar CoreCharType

        body <>= [StoreC tmp '(', PrintC tmp]

        Some1 fst <- callFunWith "fst" [Some1 arg]
        fst' <- unsafeCast fst elemT1
        genPrintCoreInstr fst'

        body <>= [StoreC tmp ',', PrintC tmp]

        Some1 snd <- callFunWith "snd" [Some1 arg]
        snd' <- unsafeCast snd elemT1
        genPrintCoreInstr snd'

        body <>= [StoreC tmp ')', PrintC tmp]
    genPrintCoreInstr _ = coreError

toConstrained :: (MonadFail m, HasCallStack) => CoreType a -> m (Constrained GenTConFun CoreType a)
toConstrained CoreIntType = pure (Constrained CoreIntType)
toConstrained CoreBoolType = pure (Constrained CoreBoolType)
toConstrained CoreCharType = pure (Constrained CoreCharType)
toConstrained CoreVoidType = pure (Constrained CoreVoidType)
toConstrained (CoreListType elemT) = do
    Constrained elemT' <- toConstrained elemT
    pure . Constrained $ CoreListType elemT'
toConstrained (CoreTupleType elemT1 elemT2) = do
    Constrained elemT1' <- toConstrained elemT1
    Constrained elemT2' <- toConstrained elemT2
    pure . Constrained $ CoreTupleType elemT1' elemT2'
toConstrained t = fail $
    "Cannot generate overloaded constraint for this type: " <> show t

solveFunDeclConstraints :: CoreFunDecl xs r -> CoreMonad [Some1 CoreFunDef]
solveFunDeclConstraints (CoreFunDecl _ args _) = do
    forM (hListToList args) $ \(Some1 (Var id (CoreFunType (varT :+: _) _))) -> do
        Constrained varT' <- toConstrained varT
        body .= []
        case T.unpack id of
            ('\'':'e':'q':'_':'c':'o':'n':_) -> do
                funName <- mkLabel "eq_con"
                let arg1 = Var "x" varT
                    arg2 = Var "y" varT
                    funDecl' = CoreFunDecl' (CoreFunDecl funName (arg1 :+: arg2 :+: HNil) CoreBoolType)
                dst <- genEqCoreInstr arg1 arg2
                body <>= [RetV dst]
                funBody <- use body
                return . Some1 $ CoreFunDef funDecl' funBody
            ('\'':'o':'r':'d':'_':'c':'o':'n':_) -> do
                funName <- mkLabel "ord_con"
                let arg1 = Var "x" varT
                    arg2 = Var "y" varT
                    funDecl' = CoreFunDecl' (CoreFunDecl funName (arg1 :+: arg2 :+: HNil) CoreBoolType)
                dst <- genOrdCoreInstr arg1 arg2
                body <>= [RetV dst]
                funBody <- use body
                return . Some1 $ CoreFunDef funDecl' funBody
            ('\'':'p':'r':'i':'n':'t':'_':'c':'o':'n':_) -> do
                funName <- mkLabel "print_con"
                let arg = Var "x" varT
                    funDecl' = CoreFunDecl' (CoreFunDecl funName (arg :+: HNil) CoreVoidType)
                genPrintCoreInstr arg
                dst <- mkTmpVar CoreVoidType
                body <>= [RetV dst]
                funBody <- use body
                return . Some1 $ CoreFunDef funDecl' funBody
            _ -> coreError
