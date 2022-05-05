{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.CodeGen.CoreLangGenLib where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import GHC.Stack
import Control.Applicative

import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.Common.TypeFunc (Some1(..), HList(..))
import qualified SPL.Compiler.SemanticAnalysis.TCT as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck as TCT

type Error = Text
data CoreState = CoreState {
    _vars :: Some1 (HList Var),
    _funcs :: Some1 (HList CoreFunDecl'),
    _body :: [CoreInstr],
    _varCounter :: Int,
    _labelCounter :: Int
}

makeLenses ''CoreState

type CoreMonad a = HasCallStack => StateT CoreState (Either Error) a

withCleanState :: CoreMonad a -> CoreMonad a
withCleanState action = do
    body .= []
    a <- action
    body .= []
    pure a

stackTrace :: HasCallStack => Text
stackTrace = T.pack (prettyCallStack callStack)

instance MonadFail (Either Error) where
    fail err = Left $ T.pack err <> "\n" <> stackTrace
    
coreError :: CoreMonad a
coreError = lift $ 
    Left $ "Internal core error: \n" <> stackTrace

pureCoreError :: HasCallStack => a
pureCoreError = error . T.unpack $ 
    "Internal core error: \n" <> stackTrace

mkName :: CoreMonad Identifier
mkName = do
    c <- use varCounter
    varCounter += 1
    return $ "'tmp" <> T.pack (show c)

mkLabel :: Text -> CoreMonad Label
mkLabel prefix = do
    c <- use labelCounter
    labelCounter += 1
    return $ prefix <> T.pack (show c) 

mkTmpVar :: CoreType a -> CoreMonad (Var a)
mkTmpVar ct = do
    id <- mkName
    someCtx <- use vars
    case someCtx of
        Some1 ctx' -> pure $ Var id ct

unsafeCast :: Var a -> CoreType b -> CoreMonad (Var b)
unsafeCast var@(Var varId _) t = do
    tmp <- mkTmpVar t
    body <>= [StoreVUnsafe tmp var ]
    return tmp

copyV :: Var a -> CoreMonad (Var a)
copyV var@(Var id ct) = do
    newVar <- mkTmpVar ct
    body <>= [Declare var, StoreV newVar var]
    return newVar

getRef :: Var a -> CoreMonad (Var (Ptr a))
getRef var = do
    varRef <- mkTmpVar (CorePtrType $ var ^. varType)
    body <>= [Declare varRef, Ref varRef var]
    return varRef

whenCoreTypeEq :: CoreType a -> 
                  CoreType b -> 
                  (CoreType a -> CoreType a -> CoreMonad c) -> 
                  CoreMonad c
whenCoreTypeEq v1@CoreIntType v2@CoreIntType f = f v1 v2
whenCoreTypeEq v1@CoreBoolType v2@CoreBoolType f = f v1 v2
whenCoreTypeEq v1@CoreCharType v2@CoreCharType f = f v1 v2
whenCoreTypeEq v1@CoreUnknownType v2@CoreUnknownType f = f v1 v2
whenCoreTypeEq v1@CoreVoidType v2@CoreVoidType f = f v1 v2
whenCoreTypeEq (CorePtrType ta) (CorePtrType tb) f = 
    whenCoreTypeEq ta tb (\ta' tb' -> f (CorePtrType ta') (CorePtrType tb'))
whenCoreTypeEq (CoreListType ta) (CoreListType tb) f = 
    whenCoreTypeEq ta tb (\ta' tb' -> f (CoreListType ta') (CoreListType tb'))
whenCoreTypeEq (CoreTupleType ta1 ta2) (CoreTupleType tb1 tb2) f =
    whenCoreTypeEq ta1 tb1 $ \ta1' tb1' ->
        whenCoreTypeEq ta2 tb2 $ \ta2' tb2' ->
            f (CoreTupleType ta1' ta2') (CoreTupleType tb1' tb2')
whenCoreTypeEq (CoreFunType ta1 ta2) (CoreFunType tb1 tb2) f =
    whenCoreTypeEq ta1 tb1 $ \ta1' tb1' ->
        whenCoreTypeEq ta2 tb2 $ \ta2' tb2' ->
            f (CoreFunType ta1' ta2') (CoreFunType tb1' tb2')
whenCoreTypeEq _ _ _ = coreError

whenVarTEq :: Var a -> Var b -> (Var a -> Var a -> CoreMonad c) -> CoreMonad c
whenVarTEq v1@(Var v1id ta) v2@(Var v2id tb) f = 
    whenCoreTypeEq ta tb $ \ta' tb' -> f (Var v1id ta') (Var v2id tb')

whenVar3TEq :: Var a -> Var b -> Var c -> (Var a -> Var a -> Var a -> CoreMonad c) -> CoreMonad c
whenVar3TEq v1@(Var v1id ta) v2@(Var v2id tb) v3@(Var v3id tc) f = 
    whenCoreTypeEq ta tb $ \ta' tb' -> 
        whenCoreTypeEq ta' tc $ \ta'' tc' -> 
            f (Var v1id ta'') (Var v2id tb') (Var v3id tc')

whenVarTListEq :: Var (Ptr [a]) -> Var b -> (Var (Ptr [a]) -> Var a -> CoreMonad c) -> CoreMonad c
whenVarTListEq (Var v1id ta) (Var v2id tb) f = 
    whenCoreTypeEq ta (CoreListType tb) $ 
        \ta' (CoreListType tb') -> f (Var v1id ta') (Var v2id tb')

whenListVarTEq :: HList Var xs -> HList Var ys -> (HList Var xs -> HList Var xs -> CoreMonad c) -> CoreMonad c
whenListVarTEq HNil HNil f = f HNil HNil
whenListVarTEq (x :+: xs) (y :+: ys) f =
    whenVarTEq x y $ \x' y' -> do
        whenListVarTEq xs ys $ \xs' ys' ->
            f (x' :+: xs') (y' :+: ys')
whenListVarTEq _ _ _ = coreError

findFun :: Identifier -> CoreMonad (Some1 CoreFunDecl')
findFun id = do
    Some1 funDecls <- use funcs
    findFun' funDecls id

    where
        findFun' :: HList CoreFunDecl' xs -> Identifier -> CoreMonad (Some1 CoreFunDecl')
        findFun' HNil _ = coreError
        findFun' (CoreFunDecl' f :+: rest) id
            | f ^. funId == id = return $ Some1 (CoreFunDecl' f)
            | otherwise = findFun' rest id

findVar :: Identifier -> CoreMonad (Some1 Var)
findVar id = do
    Some1 varCtx <- use vars
    findVar' varCtx
    where
        findVar' :: HList Var xs -> CoreMonad (Some1 Var)
        findVar' HNil = coreError
        findVar' (v@(Var vid _) :+: rest)
            | vid == id = pure (Some1 v)
            | otherwise = findVar' rest

