{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
module SPL.Compiler.CodeGen.IRLangTConGen where

import qualified Data.Text as T
import qualified Data.List as L
import Control.Lens
import Control.Monad
import Data.Proxy
import GHC.Stack

import SPL.Compiler.CodeGen.IRLang
import SPL.Compiler.CodeGen.IRLangGenLib
import SPL.Compiler.Common.TypeFunc
import Data.Bifunctor (first)

class GenTConFun a where
    genEqIRInstr    :: IRType a -> IRMonad (IRFunDef '[a, a, Bool], [Some1 IRFunDecl'])
    genOrdIRInstr   :: IRType a -> IRMonad (IRFunDef '[a, a, Bool], [Some1 IRFunDecl'])
    genPrintIRInstr :: IRType a -> IRMonad (IRFunDef '[a, Unit],    [Some1 IRFunDecl'])

printString :: String -> [IRInstr]
printString = map (PrintC . IRLit . IRChar)

mkEqOrdFunDecl :: Identifier -> IRType a -> IRFunDecl '[a, a] Bool
mkEqOrdFunDecl funName elemT =
    let arg1 = Var "x" elemT Local
        arg2 = Var "y" elemT Local
    in IRFunDecl funName (arg1 :+: arg2 :+: HNil) IRBoolType

mkEqFunDecl :: IRType a -> IRFunDecl '[a, a] Bool
mkEqFunDecl elemT = mkEqOrdFunDecl (mkEqFunName elemT) elemT

mkOrdFunDecl :: IRType a -> IRFunDecl '[a, a] Bool
mkOrdFunDecl elemT = mkEqOrdFunDecl (mkOrdFunName elemT) elemT

mkPrintFunDecl :: IRType a -> IRFunDecl '[a] Unit
mkPrintFunDecl elemT =
    let arg1 = Var "x" elemT Local
        arg2 = Var "y" elemT Local
    in IRFunDecl (mkPrintFunName elemT) (arg1 :+: HNil) IRVoidType

mkEqFunName :: IRType a -> Identifier
mkEqFunName t = "_eq_tcon_" <> textifyType t

mkOrdFunName :: IRType a -> Identifier
mkOrdFunName t = "_ord_tcon_" <> textifyType t

mkPrintFunName :: IRType a -> Identifier
mkPrintFunName t = "_print_tcon_" <> textifyType t

textifyType :: IRType a -> Identifier
textifyType IRIntType = "i"
textifyType IRBoolType = "b"
textifyType IRCharType = "c"
textifyType IRVoidType = "v"
textifyType (IRUnknownType txt) = "u"
textifyType (IRPtrType t) = "ptr_" <> textifyType t <> "_"
textifyType (IRListType t) = "list_" <> textifyType t <> "_"
textifyType (IRFunType hl r) =
    "fun_" <> T.intercalate "_" (hListMapToList textifyType hl) <> "_" <> textifyType r <> "_"
textifyType (IRTupleType a b) = "tup_" <> textifyType a <> "_" <> textifyType b <> "_"

instance GenTConFun Unit where
    genEqIRInstr t =
        let funDecl = mkEqFunDecl t
        in return (IRFunDef (IRFunDecl' funDecl) [Ret (IRLit $ IRBool True)], [])

    genOrdIRInstr t =
        let funDecl = mkOrdFunDecl t
        in return (IRFunDef (IRFunDecl' funDecl) [Ret (IRLit $ IRBool True)], [])

    genPrintIRInstr t =
        let funDecl = mkPrintFunDecl t
        in return (IRFunDef (IRFunDecl' funDecl) (printString "Void" ++ [Ret (IRLit IRVoid)]), [])

instance GenTConFun Int where
    genEqIRInstr t = do
        let funDecl@(IRFunDecl _ (arg1 :+: arg2 :+: HNil) _) = mkEqFunDecl t
        funBody <- declareBodyAs $ do
            tmp <- mkTmpVar IRBoolType
            body <>= [Eq tmp (IRVar arg1) (IRVar arg2), Ret (IRVar tmp)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [])

    genOrdIRInstr t = do
        let funDecl@(IRFunDecl _ (arg1 :+: arg2 :+: HNil) _) = mkOrdFunDecl t
        funBody <- declareBodyAs $ do
            tmp <- mkTmpVar IRBoolType
            body <>= [Lt tmp (IRVar arg1) (IRVar arg2), Ret (IRVar tmp)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [])

    genPrintIRInstr t =
        let funDecl@(IRFunDecl _ (arg1 :+: HNil) _) = mkPrintFunDecl t
        in return (IRFunDef (IRFunDecl' funDecl) [PrintI (IRVar arg1), Ret (IRLit IRVoid)], [])

instance GenTConFun Bool where
    genEqIRInstr t = do
        let funDecl@(IRFunDecl _ (arg1 :+: arg2 :+: HNil) _) = mkEqFunDecl t
        funBody <- declareBodyAs $ do
            tmp1 <- mkTmpVar IRBoolType
            tmp2 <- mkTmpVar IRBoolType
            body <>= [Xor tmp1 (IRVar arg1) (IRVar arg2), Not tmp2 (IRVar tmp1)]
            body <>= [Ret (IRVar tmp2)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [])

    genOrdIRInstr t = do
        let funDecl@(IRFunDecl _ (arg1 :+: arg2 :+: HNil) _) = mkEqFunDecl t
        funBody <- declareBodyAs $ do
            tmp1 <- mkTmpVar IRBoolType
            tmp2 <- mkTmpVar IRBoolType
            body <>= [Not tmp1 (IRVar arg1), And tmp2 (IRVar tmp1) (IRVar arg2)]
            body <>= [Ret (IRVar tmp2)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [])

    genPrintIRInstr t = do
        let funDecl@(IRFunDecl _ (arg1 :+: HNil) _) = mkPrintFunDecl t
        funBody <- declareBodyAs $ do
            printFalse <- mkLabel "PrintFalse"
            end <- mkLabel "End"
            body <>= [BrFalse (IRVar arg1) printFalse]
            body <>= printString "True"
            body <>= [BrAlways end]
            body <>= [SetLabel printFalse]
            body <>= printString "False"
            body <>= [SetLabel end]
            body <>= [Ret (IRLit IRVoid)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [])

instance GenTConFun Char where
    genEqIRInstr t = do
        let funDecl@(IRFunDecl _ (arg1 :+: arg2 :+: HNil) _) = mkEqFunDecl t
        funBody <- declareBodyAs $ do
            tmp1 <- mkTmpVar IRIntType
            tmp2 <- mkTmpVar IRIntType
            res <- mkTmpVar IRBoolType
            body <>= [Cast tmp1 (IRVar arg1),
                      Cast tmp2 (IRVar arg2),
                      Eq res (IRVar tmp1) (IRVar tmp2),
                      Ret (IRVar res)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [])

    genOrdIRInstr t = do
        let funDecl@(IRFunDecl _ (arg1 :+: arg2 :+: HNil) _) = mkEqFunDecl t
        funBody <- declareBodyAs $ do
            tmp1 <- mkTmpVar IRIntType
            tmp2 <- mkTmpVar IRIntType
            res <- mkTmpVar IRBoolType
            body <>= [Cast tmp1 (IRVar arg1),
                      Cast tmp2 (IRVar arg2),
                      Lt res (IRVar tmp1) (IRVar tmp2),
                      Ret (IRVar tmp2)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [])

    genPrintIRInstr t =
        let funDecl@(IRFunDecl _ (arg1 :+: HNil) _) = mkPrintFunDecl t
        in return (IRFunDef (IRFunDecl' funDecl) [PrintC (IRVar arg1), Ret (IRLit IRVoid)], [])

genListEqOrdIRInstr :: (forall a. IRType a -> IRFunDecl '[a, a] Bool) ->
                    IRType (Ptr [b]) -> IRMonad (IRFunDef '[Ptr [b], Ptr [b], Bool], [Some1 IRFunDecl'])
genListEqOrdIRInstr f t@(IRListType t1) = do
        let funDecl@(IRFunDecl _ (arg1 :+: arg2 :+: HNil) _) = f t
            innerFunDecl1 = f t1
        funBody <- declareBodyAs $ do
            end <- mkLabel "End"
            whileStart <- mkLabel "WhileStart"

            result <- mkTmpVar IRBoolType
            body <>= [StoreV result (IRLit $ IRBool True)]
            tmp <- mkTmpVar IRBoolType
            body <>= [SetLabel whileStart]

            Some1 isEmpty1'@(Var _ IRBoolType _) <- callFunByName "isEmpty" [Some1 (IRVar arg1)]
            Some1 isEmpty2'@(Var _ IRBoolType _) <- callFunByName "isEmpty" [Some1 (IRVar arg2)]

            let isEmpty1 = IRVar isEmpty1'
                isEmpty2 = IRVar isEmpty2'
            body <>= [And result isEmpty1 isEmpty2, BrTrue (IRVar result) end]
            body <>= [Not tmp isEmpty1, And tmp (IRVar tmp) isEmpty2, BrTrue (IRVar tmp) end]
            body <>= [Not tmp isEmpty2, And tmp isEmpty1 (IRVar tmp), BrTrue (IRVar tmp) end]

            Some1 hd1 <- callFunByName "hd" [Some1 (IRVar arg1)]
            hd1' <- castVar hd1 t1
            Some1 hd2 <- callFunByName "hd" [Some1 (IRVar arg2)]
            hd2' <- castVar hd2 t1

            body <>= [Call result (IRLit $ IRFun innerFunDecl1) (IRVar hd1' :+: IRVar hd2' :+: HNil)]
            body <>= [BrFalse (IRVar result) end]

            Some1 tl1 <- callFunByName "tl" [Some1 (IRVar arg1)]
            tl1' <- castVar tl1 t
            Some1 tl2 <- callFunByName "tl" [Some1 (IRVar arg2)]
            tl2' <- castVar tl1 t

            body <>= [StoreV arg1 (IRVar tl1'), StoreV arg2 (IRVar tl2')]
            body <>= [BrAlways whileStart]

            body <>= [SetLabel end]
            body <>= [Ret (IRVar result)]

        return (IRFunDef (IRFunDecl' funDecl) funBody, [Some1 (IRFunDecl' innerFunDecl1)])

genListEqOrdIRInstr _ IRPtrType{} = error "impossible"

instance GenTConFun a => GenTConFun (Ptr [a]) where
    genEqIRInstr = genListEqOrdIRInstr mkEqFunDecl
    genOrdIRInstr = genListEqOrdIRInstr mkOrdFunDecl
    genPrintIRInstr t@(IRListType t1) = do
        let funDecl@(IRFunDecl _ (arg :+: HNil) _) = mkPrintFunDecl t
            innerFunDecl1 = mkPrintFunDecl t1
        funBody <- declareBodyAs $ do
            whileStart <- mkLabel "WhileStart"
            end <- mkLabel "End"

            voidVar <- getVoidVar
            body <>= printString "["

            body <>= [SetLabel whileStart]

            Some1 isEmpty@(Var _ IRBoolType _) <- callFunByName "isEmpty" [Some1 $ IRVar arg]

            body <>= [BrTrue (IRVar isEmpty) end]

            Some1 hd <- callFunByName "hd" [Some1 $ IRVar arg]
            hd' <- castVar hd t1

            body <>= [Call voidVar (IRLit $ IRFun innerFunDecl1) (IRVar hd' :+: HNil)]

            Some1 tl <- callFunByName "tl" [Some1 $ IRVar arg]

            Some1 isEmpty@(Var _ IRBoolType _) <- callFunByName "isEmpty" [Some1 $ IRVar tl]
            body <>= [BrTrue (IRVar isEmpty) end]
            body <>= printString " "

            tl' <- castVar tl t
            body <>= [StoreV arg (IRVar tl'), BrAlways whileStart]
            body <>= [SetLabel end]
            body <>= printString "]"
            body <>= [Ret (IRLit IRVoid)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [Some1 (IRFunDecl' innerFunDecl1)])

    genPrintIRInstr IRPtrType{} = error "impossible"

genTupEqOrdIRInstr :: (forall a. IRType a -> IRFunDecl '[a, a] Bool) ->
                    IRType (Ptr (a,b)) -> IRMonad (IRFunDef '[Ptr (a,b), Ptr (a,b), Bool], [Some1 IRFunDecl'])
genTupEqOrdIRInstr f t@(IRTupleType t1 t2) = do
    let funDecl@(IRFunDecl _ (arg1 :+: arg2 :+: HNil) _) = f t
        innerFunDecl1 = f t1
        innerFunDecl2 = f t2
    funBody <- declareBodyAs $ do
        end <- mkLabel "End"

        result <- mkTmpVar IRBoolType
        body <>= [StoreV result (IRLit $ IRBool True)]

        Some1 fst1 <- callFunByName "fst" [Some1 $ IRVar arg1]
        fst1' <- castVar fst1 t1
        Some1 fst2 <- callFunByName "fst" [Some1 $ IRVar arg2]
        fst2' <- castVar fst2 t1

        body <>= [Call result (IRLit $ IRFun innerFunDecl1) (IRVar fst1' :+: IRVar fst2' :+: HNil)]
        body <>= [BrFalse (IRVar result) end]

        Some1 snd1 <- callFunByName "snd" [Some1 $ IRVar arg1]
        snd1' <- castVar snd1 t2
        Some1 snd2 <- callFunByName "snd" [Some1 $ IRVar arg2]
        snd2' <- castVar snd2 t2

        body <>= [Call result (IRLit $ IRFun innerFunDecl2) (IRVar snd1' :+: IRVar snd2' :+: HNil)]

        body <>= [SetLabel end, Ret (IRVar result)]

    return (IRFunDef (IRFunDecl' funDecl) funBody, [Some1 (IRFunDecl' innerFunDecl1), Some1 (IRFunDecl' innerFunDecl2)])
genTupEqOrdIRInstr _ IRPtrType{} = error "impossible"

instance (GenTConFun a, GenTConFun b) => GenTConFun (Ptr (a,b)) where
    genEqIRInstr = genTupEqOrdIRInstr mkEqFunDecl
    genOrdIRInstr = genTupEqOrdIRInstr mkOrdFunDecl

    genPrintIRInstr t@(IRTupleType t1 t2) = do
        let funDecl@(IRFunDecl _ (arg :+: HNil) _) = mkPrintFunDecl t
            innerFunDecl1 = mkPrintFunDecl t1
            innerFunDecl2 = mkPrintFunDecl t2
        funBody <- declareBodyAs $ do
            body <>= printString "("
            Some1 fst <- callFunByName "fst" [Some1 $ IRVar arg]
            fst'@(Var _ fstT _)  <- castVar fst t1

            voidVar <- getVoidVar
            body <>= [Call voidVar (IRLit $ IRFun innerFunDecl1) (IRVar fst' :+: HNil)]

            body <>= printString ","

            Some1 snd <- callFunByName "snd" [Some1 $ IRVar arg]
            snd'@(Var _ sndT _) <- castVar snd t2
            body <>= [Call voidVar (IRLit $ IRFun innerFunDecl2) (IRVar snd' :+: HNil)]

            body <>= printString ")"
            body <>= [Ret (IRLit IRVoid)]
        return (IRFunDef (IRFunDecl' funDecl) funBody, [Some1 (IRFunDecl' innerFunDecl1), Some1 (IRFunDecl' innerFunDecl2)])

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

genAllFunDeclRec :: forall xs b. GenTConFun b =>
                    (forall a. GenTConFun a => IRType a -> IRMonad (Some1 IRFunDef, [Some1 IRFunDecl'])) ->
                    IRType b ->
                    IRMonad (Some1 IRFunDecl', [Some1 IRFunDef])
genAllFunDeclRec generator t = do
    (Some1 def@(IRFunDef decl _), decls) <- generator t
    funcs %= (\(Some1 env) -> Some1 $ decl :+: env)
    defs' <- concat <$> forM decls (\(Some1 f) -> do
        envDecls <- (\(Some1 hs) -> hListToList hs) <$> use funcs
        case Some1 f `shouldGenerate` envDecls of
            Nothing -> pure mempty
            Just (Some1 t') -> do
                Constrained t'' <- toConstrained t'
                snd <$> genAllFunDeclRec generator t'')

    return (Some1 decl, Some1 def : defs')

    where
        getEnvFuncNames :: IRMonad [Identifier]
        getEnvFuncNames = use funcs >>= (\(Some1 env) -> pure $ hListMapToList getId env)

        getId :: IRFunDecl' xs -> Identifier
        getId (IRFunDecl' (IRFunDecl id _ _)) = id

        shouldGenerate :: Some1 IRFunDecl' -> [Some1 IRFunDecl'] -> Maybe (Some1 IRType)
        shouldGenerate (Some1 (IRFunDecl' (IRFunDecl id ((Var _ t _) :+: _) _))) ys =
            if id `elem` map (\(Some1 y) -> getId y) ys then
                Nothing
            else
               Just $ Some1 t
        shouldGenerate _ _ = Nothing

genAllEqFunDeclRec :: GenTConFun a => IRType a -> IRMonad (Some1 IRFunDecl', [Some1 IRFunDef])
genAllEqFunDeclRec = genAllFunDeclRec (fmap (first Some1) . genEqIRInstr)

genAllOrdFunDeclRec :: GenTConFun a => IRType a -> IRMonad (Some1 IRFunDecl', [Some1 IRFunDef])
genAllOrdFunDeclRec = genAllFunDeclRec (fmap (first Some1) . genOrdIRInstr)

genAllPrintFunDeclRec :: GenTConFun a => IRType a -> IRMonad (Some1 IRFunDecl', [Some1 IRFunDef])
genAllPrintFunDeclRec = genAllFunDeclRec (fmap (first Some1) . genPrintIRInstr)

solveTConConstraint :: Some1 TCon -> IRMonad [Some1 IRFunDef]
solveTConConstraint (Some1 tcon) = do
    case tcon of
        TEq varT -> do
            Constrained varT' <- toConstrained varT
            snd <$> genAllEqFunDeclRec varT
        TOrd varT -> do
            Constrained varT' <- toConstrained varT
            snd <$> genAllOrdFunDeclRec varT
        TPrint varT -> do
            Constrained varT' <- toConstrained varT
            snd <$> genAllPrintFunDeclRec varT
