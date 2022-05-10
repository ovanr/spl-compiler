{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.CodeGen.CoreLangGenLib where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.Set as S
import Data.Bifunctor
import Data.Either
import Control.Lens hiding (Snoc)
import Control.Monad.State
import GHC.Stack
import Control.Applicative

import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.Common.TypeFunc
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

stackTrace :: HasCallStack => String
stackTrace = prettyCallStack callStack

instance MonadFail (Either ()) where
    fail _ = Left ()

instance MonadFail (Either Error) where
    fail err = Left $
        "Internal core error: " <> T.pack err <> "\n"

coreErrorWithDesc :: (HasCallStack, MonadFail m) => Error -> m a
coreErrorWithDesc err = fail (T.unpack err <> "\n" <> stackTrace)

coreError :: (HasCallStack, MonadFail m) => m a
coreError = fail stackTrace

pureCoreError :: HasCallStack => a
pureCoreError = error $ "Internal core error: \n" <> stackTrace

mkName :: Identifier -> CoreMonad Identifier
mkName prefix = do
    c <- use varCounter
    varCounter += 1
    return $ "0" <> prefix <> T.pack (show c)

mkLabel :: Text -> CoreMonad Label
mkLabel prefix = do
    c <- use labelCounter
    labelCounter += 1
    return $ prefix <> T.pack (show c)

mkTmpVar :: CoreType a -> CoreMonad (Var a)
mkTmpVar ct = do
    id <- mkName "tmp"
    let var = Var id ct
    body <>= [Declare var]
    pure var

unsafeCast :: Var a -> CoreType b -> CoreMonad (Var b)
unsafeCast var@(Var varId varT) resultType = do
    ifCoreTypeEq resultType varT
        (\resultType' _ -> return (Var varId resultType'))
        (\_ -> do
            tmp <- mkTmpVar resultType
            body <>= [StoreVUnsafe tmp var ]
            return tmp)

copyV :: Var a -> CoreMonad (Var a)
copyV var@(Var id ct) = do
    newVar <- mkTmpVar ct
    body <>= [StoreV newVar var]
    return newVar

getRef :: Var a -> CoreMonad (Var (Ptr a))
getRef var = do
    varRef <- mkTmpVar (CorePtrType $ var ^. varType)
    body <>= [Ref varRef var]
    return varRef

ifCoreTypeEq :: forall a b c.
                CoreType a ->
                CoreType b ->
                (CoreType a -> CoreType a -> c) ->
                (CoreType a -> c) ->
                c
ifCoreTypeEq ta tb f g = fromRight (g ta)
    (whenCoreTypeEq ta tb (\ta tb -> Right (f ta tb)) :: Either () c)

whenCoreTypeEq :: (HasCallStack, MonadFail m) =>
                  CoreType a ->
                  CoreType b ->
                  (CoreType a -> CoreType a -> m c) ->
                  m c
whenCoreTypeEq v1@CoreIntType v2@CoreIntType f = f v1 v2
whenCoreTypeEq v1@CoreBoolType v2@CoreBoolType f = f v1 v2
whenCoreTypeEq v1@CoreCharType v2@CoreCharType f = f v1 v2
whenCoreTypeEq v1@(CoreUnknownType a1) v2@(CoreUnknownType a2) f | a1 == a2 = f v1 v2
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
    whenListCoreTypeEq ta1 tb1 $ \ta1' tb1' ->
        whenCoreTypeEq ta2 tb2 $ \ta2' tb2' ->
            f (CoreFunType ta1' ta2') (CoreFunType tb1' tb2')
whenCoreTypeEq ta tb _ = fail $
    "Unexpected Type mismatch: " <>
    show ta <> " /= " <> show tb <> "\n" <> stackTrace

whenListCoreTypeEq :: (HasCallStack, MonadFail m) =>
                      HList CoreType xs ->
                      HList CoreType ys ->
                      (HList CoreType xs -> HList CoreType xs -> m c)
                      -> m c
whenListCoreTypeEq HNil HNil f = f HNil HNil
whenListCoreTypeEq (x :+: xs) (y :+: ys) f =
    whenCoreTypeEq x y $ \x' y' -> do
        whenListCoreTypeEq xs ys $ \xs' ys' ->
            f (x' :+: xs') (y' :+: ys')
whenListCoreTypeEq ta tb _ = fail $
    "Unexpected type list mismatch: " <>
    show (hListLength ta) <> " /= " <> show (hListLength tb) <>
    "\n" <> stackTrace

whenVarTEq :: (HasCallStack, MonadFail m) => Var a -> Var b -> (Var a -> Var a -> m c) -> m c
whenVarTEq v1@(Var v1id ta) v2@(Var v2id tb) f =
    whenCoreTypeEq ta tb $ \ta' tb' -> f (Var v1id ta') (Var v2id tb')

whenVar3TEq :: (HasCallStack, MonadFail m) => Var a -> Var b -> Var c -> (Var a -> Var a -> Var a -> m c) -> m c
whenVar3TEq v1@(Var v1id ta) v2@(Var v2id tb) v3@(Var v3id tc) f =
    whenCoreTypeEq ta tb $ \ta' tb' ->
        whenCoreTypeEq ta' tc $ \ta'' tc' ->
            f (Var v1id ta'') (Var v2id tb') (Var v3id tc')

whenVarTListEq :: (HasCallStack, MonadFail m) => Var (Ptr [a]) -> Var b -> (Var (Ptr [a]) -> Var a -> m c) -> m c
whenVarTListEq (Var v1id ta) (Var v2id tb) f =
    whenCoreTypeEq ta (CoreListType tb) $
        \ta' (CoreListType tb') -> f (Var v1id ta') (Var v2id tb')

whenListVarTEq :: (HasCallStack, MonadFail m) => HList Var xs -> HList Var ys -> (HList Var xs -> HList Var xs -> m c) -> m c
whenListVarTEq HNil HNil f = f HNil HNil
whenListVarTEq (x :+: xs) (y :+: ys) f =
    whenVarTEq x y $ \x' y' -> do
        whenListVarTEq xs ys $ \xs' ys' ->
            f (x' :+: xs') (y' :+: ys')
whenListVarTEq ta tb _ = fail $
    "Unexpected variable list mismatch: " <>
    show (hListLength ta) <> " /= " <> show (hListLength tb) <>
    "\n" <> stackTrace

whenFunTEq :: (HasCallStack, MonadFail m) =>
              CoreFunDecl as1 r1 ->
              CoreType (Ptr (as2 --> r2)) ->
              (CoreFunDecl as2 r2 -> m c)
              -> m c
whenFunTEq (CoreFunDecl label funArgs funRet) (CoreFunType argT retT) f =
    whenListVarTEq (hListZip2 (\t' (Var id _) -> Var id t') (Var "") argT funArgs) funArgs $
        \funArgs' _ ->
            whenCoreTypeEq retT funRet $
                \retT' _ -> f $ CoreFunDecl label funArgs' retT'
whenFunTEq _ _ _ = coreError

ifFunTypeEq :: forall as1 r1 as2 r2 c.
               CoreFunDecl as1 r1 ->
               CoreType (Ptr (as2 --> r2)) ->
               (CoreFunDecl as2 r2 -> c) ->
               c ->
               c
ifFunTypeEq decl expT f g = fromRight g
    (whenFunTEq decl expT (Right . f) :: Either () c)

tctTypeToCoreType :: TCT.TCTType -> Some1 CoreType
tctTypeToCoreType TCT.TCTIntType{} = Some1 CoreIntType
tctTypeToCoreType TCT.TCTBoolType{} = Some1 CoreBoolType
tctTypeToCoreType TCT.TCTCharType{} = Some1 CoreCharType
tctTypeToCoreType TCT.TCTVoidType{} = Some1 CoreVoidType
tctTypeToCoreType (TCT.TCTVarType _ _ tvar) = Some1 (CoreUnknownType tvar)
tctTypeToCoreType (TCT.TCTTupleType _ _ ta tb) =
    case (tctTypeToCoreType ta, tctTypeToCoreType tb) of
        (Some1 ta', Some1 tb') -> Some1 (CoreTupleType ta' tb')
tctTypeToCoreType (TCT.TCTListType _ _ ta) =
    case tctTypeToCoreType ta of
        Some1 ta' -> Some1 (CoreListType ta')
tctTypeToCoreType t@(TCT.TCTFunType _ tcon _ _) =
    let (args, return) = TCT.decomposeFunType t
    in case (hListMapFromList tctTConToCoreType (S.toList tcon),
             hListFromList $ map tctTypeToCoreType args,
             tctTypeToCoreType return) of
        (Some1 tcon', Some1 ta', Some1 tb') -> Some1 (CoreFunType (tcon' +++ ta') tb')

tctTConToCoreType :: TCT.TCon -> Some1 CoreType
tctTConToCoreType (TCT.TPrint t) =
    case tctTypeToCoreType t of
        Some1 t' -> Some1 $ CoreFunType (t' :+: HNil) CoreVoidType
tctTConToCoreType (TCT.TEq t) =
    case tctTypeToCoreType t of
        Some1 t' -> Some1 $ CoreFunType (t' :+: t' :+: HNil) CoreBoolType
tctTConToCoreType (TCT.TOrd t) =
    case tctTypeToCoreType t of
        Some1 t' -> Some1 $ CoreFunType (t' :+: t' :+: HNil) CoreBoolType

castFunArg :: Var a -> Var b -> CoreMonad (Var a)
castFunArg arg@(Var _ argT) concreteArg = do
    if hasUnknownType argT then do
        concreteArg' <- mkTmpVar argT
        body <>= [StoreVUnsafe concreteArg' concreteArg]
        pure concreteArg'
    else
        whenVarTEq arg concreteArg $ \arg' concreteArg' -> return concreteArg'

castFunArgs :: HList Var xs -> [Some1 Var] -> CoreMonad (HList Var xs)
castFunArgs HNil [] = pure HNil
castFunArgs (arg :+: args) (Some1 concreteArg:concreteArgs) = do
    concreteArg' <- castFunArg arg concreteArg
    concreteArgs' <- castFunArgs args concreteArgs
    return (concreteArg' :+: concreteArgs')
castFunArgs hs ys = coreErrorWithDesc . T.pack $
    "Mismatched number of function arguments: " <>
    show (hListLength hs) <> " /= " <> show (length ys)

callFunWith :: Identifier -> [Some1 Var] -> CoreMonad (Some1 Var)
callFunWith funName args = do
    Some1 (CoreFunDecl' fun) <- findFunByName funName
    args' <- castFunArgs (fun ^. funArgs) args
    dst <- mkTmpVar (fun ^. funRetType)
    body <>= [ Call dst fun args' ] 
    return (Some1 dst)

findFunByName :: Identifier -> CoreMonad (Some1 CoreFunDecl')
findFunByName id = do
    Some1 funDecls <- use funcs
    findFunByName' funDecls id

    where
        findFunByName' :: HList CoreFunDecl' xs -> Identifier -> CoreMonad (Some1 CoreFunDecl')
        findFunByName' HNil _ = coreErrorWithDesc $ "Unable to find function: " <> id
        findFunByName' (CoreFunDecl' f :+: rest) id
            | f ^. funId == id = return $ Some1 (CoreFunDecl' f)
            | otherwise = findFunByName' rest id

getFunType :: CoreFunDecl xs a -> CoreType (Ptr (xs --> a))
getFunType (CoreFunDecl _ args ret) = CoreFunType (hListTCMap _varType args) ret

findFun :: forall as r. (Identifier -> Bool) -> CoreType (Ptr (as --> r)) -> CoreMonad (CoreFunDecl as r)
findFun pred reqT@CoreFunType{} = do
    Some1 funDecls <- use funcs
    findFun' funDecls

    where
        findFun' :: HList CoreFunDecl' xs -> CoreMonad (CoreFunDecl as r)
        findFun' HNil = coreError
        findFun' (CoreFunDecl' f :+: rest)
            | pred (f ^. funId) =
                ifFunTypeEq f reqT return (findFun' rest)
            | otherwise = findFun' rest
findFun _ _ = coreError

searchFunByName :: (Identifier -> Bool) -> CoreMonad (Maybe (Some1 CoreFunDecl')) 
searchFunByName pred = do
    Some1 funDecls <- use funcs
    pure $ searchByName funDecls

    where
        searchByName :: HList CoreFunDecl' xs -> Maybe (Some1 CoreFunDecl')
        searchByName HNil = Nothing
        searchByName (CoreFunDecl' f :+: rest)
            | pred (f ^. funId) = Just $ Some1 (CoreFunDecl' f)
            | otherwise = searchByName rest

    
findVarByName :: Identifier -> CoreMonad (Some1 Var)
findVarByName id = findVarByPred (\(Var varId _) -> varId == id)

findVar :: forall a. (Identifier -> Bool) -> CoreType a -> CoreMonad (Var a)
findVar f reqT = do
    Some1 varCtx <- use vars
    findVar' varCtx
    where
        findVar' :: HList Var xs -> CoreMonad (Var a)
        findVar' HNil = coreError
        findVar' (v@(Var varId varT) :+: rest)
            | f varId = do
                ifCoreTypeEq reqT varT (\reqT' varT' -> return (Var varId varT'))
                                               (const (findVar' rest))
            | otherwise = findVar' rest


findVarByPred :: (forall a. Var a -> Bool) -> CoreMonad (Some1 Var)
findVarByPred f = do
    Some1 varCtx <- use vars
    findVarByPred' varCtx
    where
        findVarByPred' :: HList Var xs -> CoreMonad (Some1 Var)
        findVarByPred' HNil = coreError
        findVarByPred' (v :+: rest)
            | f v = pure $ Some1 v
            | otherwise = findVarByPred' rest

findConVar :: TCT.TCon -> CoreMonad (Some1 Var)
findConVar tcon =
    case tctTConToCoreType tcon of
        Some1 tconT ->
            case tcon of
                TCT.TPrint _ -> findVarByPred $ \(Var id varT) ->
                    ifCoreTypeEq tconT varT (\_ _ -> T.isPrefixOf "0print_con" id) (const False)
                TCT.TEq _ -> findVarByPred $ \(Var id varT) ->
                    ifCoreTypeEq tconT varT (\_ _ -> T.isPrefixOf "0eq_con" id) (const False)
                TCT.TOrd _ -> findVarByPred $ \(Var id varT) ->
                    ifCoreTypeEq tconT varT (\_ _ -> T.isPrefixOf "0ord_con" id) (const False)

declareBodyAs :: CoreMonad () -> CoreMonad [CoreInstr]
declareBodyAs st = do
    body .= []
    st
    result <- use body
    body .= []
    return result

