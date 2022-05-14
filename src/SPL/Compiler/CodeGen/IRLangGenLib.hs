{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.CodeGen.IRLangGenLib where

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

import SPL.Compiler.CodeGen.IRLang
import SPL.Compiler.Common.TypeFunc
import qualified SPL.Compiler.SemanticAnalysis.TCT as TCT
import qualified SPL.Compiler.SemanticAnalysis.TypeCheck as TCT

type Error = Text
data IRState = IRState {
    _vars :: Some1 (HList Var),
    _funcs :: Some1 (HList IRFunDecl'),
    _body :: [IRInstr],
    _varCounter :: Int,
    _labelCounter :: Int
}

makeLenses ''IRState

type IRMonad a = HasCallStack => StateT IRState (Either Error) a

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

pureIRError :: HasCallStack => a
pureIRError = error $ "Internal core error: \n" <> stackTrace

mkName :: Identifier -> IRMonad Identifier
mkName prefix = do
    c <- use varCounter
    varCounter += 1
    return $ "0" <> prefix <> T.pack (show c)

mkLabel :: Text -> IRMonad Label
mkLabel prefix = do
    c <- use labelCounter
    labelCounter += 1
    return $ prefix <> T.pack (show c)

mkTmpVar :: IRType a -> IRMonad (Var a)
mkTmpVar ct = do
    id <- mkName "tmp"
    let var = Var id ct
    body <>= [Declare var]
    pure var

unsafeCast :: Var a -> IRType b -> IRMonad (Var b)
unsafeCast var@(Var varId varT) resultType = do
    ifIRTypeEq resultType varT
        (\resultType' _ -> return (Var varId resultType'))
        (\_ -> do
            tmp <- mkTmpVar resultType
            body <>= [StoreVUnsafe tmp var ]
            return tmp)

copyV :: Var a -> IRMonad (Var a)
copyV var@(Var id ct) = do
    newVar <- mkTmpVar ct
    body <>= [StoreV newVar var]
    return newVar

getRef :: Var a -> IRMonad (Var (Ptr a))
getRef var = do
    varRef <- mkTmpVar (IRPtrType $ var ^. varType)
    body <>= [Ref varRef var]
    return varRef

ifIRTypeEq :: forall a b c.
                IRType a ->
                IRType b ->
                (IRType a -> IRType a -> c) ->
                (IRType a -> c) ->
                c
ifIRTypeEq ta tb f g = fromRight (g ta)
    (whenIRTypeEq ta tb (\ta tb -> Right (f ta tb)) :: Either () c)

whenIRTypeEq :: (HasCallStack, MonadFail m) =>
                  IRType a ->
                  IRType b ->
                  (IRType a -> IRType a -> m c) ->
                  m c
whenIRTypeEq v1@IRIntType v2@IRIntType f = f v1 v2
whenIRTypeEq v1@IRBoolType v2@IRBoolType f = f v1 v2
whenIRTypeEq v1@IRCharType v2@IRCharType f = f v1 v2
whenIRTypeEq v1@(IRUnknownType a1) v2@(IRUnknownType a2) f | a1 == a2 = f v1 v2
whenIRTypeEq v1@IRVoidType v2@IRVoidType f = f v1 v2
whenIRTypeEq (IRPtrType ta) (IRPtrType tb) f =
    whenIRTypeEq ta tb (\ta' tb' -> f (IRPtrType ta') (IRPtrType tb'))
whenIRTypeEq (IRListType ta) (IRListType tb) f =
    whenIRTypeEq ta tb (\ta' tb' -> f (IRListType ta') (IRListType tb'))
whenIRTypeEq (IRTupleType ta1 ta2) (IRTupleType tb1 tb2) f =
    whenIRTypeEq ta1 tb1 $ \ta1' tb1' ->
        whenIRTypeEq ta2 tb2 $ \ta2' tb2' ->
            f (IRTupleType ta1' ta2') (IRTupleType tb1' tb2')
whenIRTypeEq (IRFunType ta1 ta2) (IRFunType tb1 tb2) f =
    whenListIRTypeEq ta1 tb1 $ \ta1' tb1' ->
        whenIRTypeEq ta2 tb2 $ \ta2' tb2' ->
            f (IRFunType ta1' ta2') (IRFunType tb1' tb2')
whenIRTypeEq ta tb _ = fail $
    "Unexpected Type mismatch: " <>
    show ta <> " /= " <> show tb <> "\n" <> stackTrace

whenListIRTypeEq :: (HasCallStack, MonadFail m) =>
                      HList IRType xs ->
                      HList IRType ys ->
                      (HList IRType xs -> HList IRType xs -> m c)
                      -> m c
whenListIRTypeEq HNil HNil f = f HNil HNil
whenListIRTypeEq (x :+: xs) (y :+: ys) f =
    whenIRTypeEq x y $ \x' y' -> do
        whenListIRTypeEq xs ys $ \xs' ys' ->
            f (x' :+: xs') (y' :+: ys')
whenListIRTypeEq ta tb _ = fail $
    "Unexpected type list mismatch: " <>
    show (hListLength ta) <> " /= " <> show (hListLength tb) <>
    "\n" <> stackTrace

whenVarTEq :: (HasCallStack, MonadFail m) => Var a -> Var b -> (Var a -> Var a -> m c) -> m c
whenVarTEq v1@(Var v1id ta) v2@(Var v2id tb) f =
    whenIRTypeEq ta tb $ \ta' tb' -> f (Var v1id ta') (Var v2id tb')

whenVar3TEq :: (HasCallStack, MonadFail m) => Var a -> Var b -> Var c -> (Var a -> Var a -> Var a -> m c) -> m c
whenVar3TEq v1@(Var v1id ta) v2@(Var v2id tb) v3@(Var v3id tc) f =
    whenIRTypeEq ta tb $ \ta' tb' ->
        whenIRTypeEq ta' tc $ \ta'' tc' ->
            f (Var v1id ta'') (Var v2id tb') (Var v3id tc')

whenVarTListEq :: (HasCallStack, MonadFail m) => Var (Ptr [a]) -> Var b -> (Var (Ptr [a]) -> Var a -> m c) -> m c
whenVarTListEq (Var v1id ta) (Var v2id tb) f =
    whenIRTypeEq ta (IRListType tb) $
        \ta' (IRListType tb') -> f (Var v1id ta') (Var v2id tb')

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
              IRFunDecl as1 r1 ->
              IRType (Ptr (as2 --> r2)) ->
              (IRFunDecl as2 r2 -> m c)
              -> m c
whenFunTEq (IRFunDecl label funArgs funRet) (IRFunType argT retT) f =
    whenListVarTEq (hListZip2 (\t' (Var id _) -> Var id t') (Var "") argT funArgs) funArgs $
        \funArgs' _ ->
            whenIRTypeEq retT funRet $
                \retT' _ -> f $ IRFunDecl label funArgs' retT'
whenFunTEq _ _ _ = coreError

ifFunTypeEq :: forall as1 r1 as2 r2 c.
               IRFunDecl as1 r1 ->
               IRType (Ptr (as2 --> r2)) ->
               (IRFunDecl as2 r2 -> c) ->
               c ->
               c
ifFunTypeEq decl expT f g = fromRight g
    (whenFunTEq decl expT (Right . f) :: Either () c)

tctTypeToIRType :: TCT.TCTType -> [TCT.TCon] -> Some1 IRType
tctTypeToIRType TCT.TCTIntType{} _ = Some1 IRIntType
tctTypeToIRType TCT.TCTBoolType{} _ = Some1 IRBoolType
tctTypeToIRType TCT.TCTCharType{} _ = Some1 IRCharType
tctTypeToIRType TCT.TCTVoidType{} _ = Some1 IRVoidType
tctTypeToIRType (TCT.TCTVarType _ tvar) _ = Some1 (IRUnknownType tvar)
tctTypeToIRType (TCT.TCTTupleType _ ta tb) _ =
    case (tctTypeToIRType ta [], tctTypeToIRType tb []) of
        (Some1 ta', Some1 tb') -> Some1 (IRTupleType ta' tb')
tctTypeToIRType (TCT.TCTListType _ ta) _ =
    case tctTypeToIRType ta [] of
        Some1 ta' -> Some1 (IRListType ta')
tctTypeToIRType t@TCT.TCTFunType{} tcons  =
    let (args, return) = TCT.decomposeFunType t
    in case (hListMapFromList tctTConToIRType tcons,
             hListFromList $ map (`tctTypeToIRType` []) args,
             tctTypeToIRType return []) of
        (Some1 tcon', Some1 ta', Some1 tb') -> Some1 (IRFunType (tcon' +++ ta') tb')

tctTConToIRType :: TCT.TCon -> Some1 IRType
tctTConToIRType (TCT.TPrint t) =
    case tctTypeToIRType t [] of
        Some1 t' -> Some1 $ IRFunType (t' :+: HNil) IRVoidType
tctTConToIRType (TCT.TEq t) =
    case tctTypeToIRType t [] of
        Some1 t' -> Some1 $ IRFunType (t' :+: t' :+: HNil) IRBoolType
tctTConToIRType (TCT.TOrd t) =
    case tctTypeToIRType t [] of
        Some1 t' -> Some1 $ IRFunType (t' :+: t' :+: HNil) IRBoolType

showVarList' :: [Some1 Var] -> String
showVarList' = concatMap (\(Some1 v) -> show v <> " ")
castFunArg :: Var a -> Var b -> IRMonad (Var a)
castFunArg arg@(Var _ argT) concreteArg = do
    if hasUnknownType argT then do
        concreteArg' <- mkTmpVar argT
        body <>= [StoreVUnsafe concreteArg' concreteArg]
        pure concreteArg'
    else
        whenVarTEq arg concreteArg $ \arg' concreteArg' -> return concreteArg'

castFunArgs :: HList Var xs -> [Some1 Var] -> IRMonad (HList Var xs)
castFunArgs HNil [] = pure HNil
castFunArgs (arg :+: args) (Some1 concreteArg:concreteArgs) = do

    concreteArg' <- castFunArg arg concreteArg
    concreteArgs' <- castFunArgs args concreteArgs
    return (concreteArg' :+: concreteArgs')
castFunArgs hs ys = coreErrorWithDesc . T.pack $
    "Mismatched number of function arguments: " <>
    show (hListLength hs) <> " /= " <> show (length ys)

showVarList :: [Some1 Var] -> String
showVarList = concatMap (\(Some1 v) -> show v <> " ")

callFunWith :: Identifier -> [Some1 Var] -> IRMonad (Some1 Var)
callFunWith funName args = do
    Some1 (IRFunDecl' fun) <- findFunByName funName
    args' <- castFunArgs (fun ^. funArgs) args
    dst <- mkTmpVar (fun ^. funRetType)
    body <>= [ Call dst fun args' ]
    return (Some1 dst)

findFunByName :: Identifier -> IRMonad (Some1 IRFunDecl')
findFunByName id = do
    Some1 funDecls <- use funcs
    findFunByName' funDecls id

    where
        findFunByName' :: HList IRFunDecl' xs -> Identifier -> IRMonad (Some1 IRFunDecl')
        findFunByName' HNil _ = coreErrorWithDesc $ "Unable to find function: " <> id
        findFunByName' (IRFunDecl' f :+: rest) id
            | f ^. funId == id = return $ Some1 (IRFunDecl' f)
            | otherwise = findFunByName' rest id

getFunType :: IRFunDecl xs a -> IRType (Ptr (xs --> a))
getFunType (IRFunDecl _ args ret) = IRFunType (hListTCMap _varType args) ret

findFun :: forall as r. (Identifier -> Bool) -> IRType (Ptr (as --> r)) -> IRMonad (IRFunDecl as r)
findFun pred reqT@IRFunType{} = do
    Some1 funDecls <- use funcs
    findFun' funDecls

    where
        findFun' :: HList IRFunDecl' xs -> IRMonad (IRFunDecl as r)
        findFun' HNil = coreError
        findFun' (IRFunDecl' f :+: rest)
            | pred (f ^. funId) =
                ifFunTypeEq f reqT return (findFun' rest)
            | otherwise = findFun' rest
findFun _ _ = coreError

searchFunByName :: (Identifier -> Bool) -> IRMonad (Maybe (Some1 IRFunDecl'))
searchFunByName pred = do
    Some1 funDecls <- use funcs
    pure $ searchByName funDecls

    where
        searchByName :: HList IRFunDecl' xs -> Maybe (Some1 IRFunDecl')
        searchByName HNil = Nothing
        searchByName (IRFunDecl' f :+: rest)
            | pred (f ^. funId) = Just $ Some1 (IRFunDecl' f)
            | otherwise = searchByName rest


findVarByName :: Identifier -> IRMonad (Some1 Var)
findVarByName id = findVarByPred (\(Var varId _) -> varId == id)

findVar :: forall a. (Identifier -> Bool) -> IRType a -> IRMonad (Var a)
findVar f reqT = do
    Some1 varCtx <- use vars
    findVar' varCtx
    where
        findVar' :: HList Var xs -> IRMonad (Var a)
        findVar' HNil = coreError
        findVar' (v@(Var varId varT) :+: rest)
            | f varId = do
                ifIRTypeEq reqT varT (\reqT' varT' -> return (Var varId varT'))
                                               (const (findVar' rest))
            | otherwise = findVar' rest


findVarByPred :: (forall a. Var a -> Bool) -> IRMonad (Some1 Var)
findVarByPred f = do
    Some1 varCtx <- use vars
    findVarByPred' varCtx
    where
        findVarByPred' :: HList Var xs -> IRMonad (Some1 Var)
        findVarByPred' HNil = coreError
        findVarByPred' (v :+: rest)
            | f v = pure $ Some1 v
            | otherwise = findVarByPred' rest

findConVar :: TCT.TCon -> IRMonad (Some1 Var)
findConVar tcon =
    case tctTConToIRType tcon of
        Some1 tconT ->
            case tcon of
                TCT.TPrint _ -> findVarByPred $ \(Var id varT) ->
                    ifIRTypeEq tconT varT (\_ _ -> T.isPrefixOf "0print_con" id) (const False)
                TCT.TEq _ -> findVarByPred $ \(Var id varT) ->
                    ifIRTypeEq tconT varT (\_ _ -> T.isPrefixOf "0eq_con" id) (const False)
                TCT.TOrd _ -> findVarByPred $ \(Var id varT) ->
                    ifIRTypeEq tconT varT (\_ _ -> T.isPrefixOf "0ord_con" id) (const False)

declareBodyAs :: IRMonad () -> IRMonad [IRInstr]
declareBodyAs st = do
    body .= []
    st
    result <- use body
    body .= []
    return result

