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

getFunType :: IRFunDecl xs a -> IRType (Ptr (xs --> a))
getFunType (IRFunDecl _ args ret) = IRFunType (hListTCMap _varType args) ret

instance Typeable Var where
    getType (Var _ t _) = t
    setType (Var v _ k) t = Var v t k

instance Typeable IRConstant where
    getType (IRInt _) = IRIntType
    getType (IRChar _) = IRCharType
    getType (IRBool _) = IRBoolType
    getType IRVoid = IRVoidType
    getType (IRFun f) = getFunType f
    setType (IRInt i) IRIntType = IRInt i
    setType (IRChar c) IRCharType = IRChar c
    setType (IRBool b) IRBoolType = IRBool b
    setType IRVoid IRVoidType = IRVoid
    setType (IRFun (IRFunDecl id args r)) (IRFunType argsT retT) = 
        IRFun (IRFunDecl id (hListZip2 (flip setType) pureIRError argsT args) retT)
    setType _ _ = pureIRError

instance Typeable Value where
    getType (IRVar v) = getType v
    getType (IRLit l) = getType l
    setType (IRVar v) t = IRVar (setType v t)
    setType (IRLit v) t = IRLit (setType v t)

instance Typeable IRType where
    getType = id
    setType _ t = t
    
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
    let var = Var id ct Temp
    body <>= [DeclareTmp var]
    pure var

castVar :: Var a -> IRType b -> IRMonad (Var b)
castVar va b = do
    IRVar v <- cast (IRVar va) b
    return v

cast :: Value a -> IRType b -> IRMonad (Value b)
cast va b = do
    ifIRTypeEq (rewriteUnknown $ getType va) (rewriteUnknown b)
        (\_ _ -> return $ setType va b)
        (\_ -> do
            Constrained2 vaT' bT' <- toCastable (getType va) (getType b)
            tmp <- mkTmpVar bT'
            body <>= [Cast tmp va]
            return (IRVar tmp))

    where
        rewriteUnknown :: IRType a -> IRType a
        rewriteUnknown (IRUnknownType _) = IRUnknownType mempty
        rewriteUnknown (IRListType t) = IRListType (rewriteUnknown t)
        rewriteUnknown (IRPtrType t) = IRPtrType (rewriteUnknown t)
        rewriteUnknown (IRTupleType a1 b1) = IRTupleType (rewriteUnknown a1) (rewriteUnknown b1)
        rewriteUnknown (IRFunType as r) = IRFunType (hListTCMap rewriteUnknown as) (rewriteUnknown r)
        rewriteUnknown t = t


copyV :: Var a -> IRMonad (Var a)
copyV var@(Var id ct _) = do
    newVar <- mkTmpVar ct
    body <>= [StoreV newVar (IRVar var)]
    return newVar

getRef :: Var a -> IRMonad (Var (Ptr a))
getRef var = do
    varRef <- mkTmpVar (IRPtrType $ var ^. varType)
    body <>= [Ref varRef var]
    return varRef

ifIRTypeEq :: forall a b c v1 v2. (Typeable v1, Typeable v2) => 
                v1 a -> v2 b -> (v1 a -> v2 a -> c) -> (v1 a -> c) -> c
ifIRTypeEq ta tb f g = fromRight (g ta)
    (whenTEq ta tb (\ta tb -> Right (f ta tb)) :: Either () c)

whenTEq :: (HasCallStack, MonadFail m, Typeable v1, Typeable v2) =>
                 v1 a -> v2 b -> (v1 a -> v2 a -> m c) -> m c
whenTEq v1 v2 f =
    case (getType v1, getType v2) of
        (IRIntType, IRIntType) -> f v1 v2
        (IRBoolType, IRBoolType) -> f v1 v2
        (IRCharType, IRCharType) -> f v1 v2
        (IRUnknownType a1, IRUnknownType a2) | a1 == a2 -> f v1 v2
        (IRVoidType, IRVoidType) -> f v1 v2
        (IRPtrType ta, IRPtrType tb) ->
            whenTEq ta tb $ \ta' tb' -> f (setType v1 (IRPtrType ta')) (setType v2 (IRPtrType tb'))
        (IRListType ta, IRListType tb) ->
            whenTEq ta tb $ \ta' tb' -> f (setType v1 (IRListType ta')) (setType v2 (IRListType tb'))
        (IRTupleType ta1 ta2, IRTupleType tb1 tb2) ->
            whenTEq ta1 tb1 $ \ta1' tb1' -> 
                whenTEq ta2 tb2 $ \ta2' tb2' -> 
                    f (setType v1 (IRTupleType ta1' ta2)) (setType v2 (IRTupleType tb1' tb2'))
        (IRFunType ta1 ta2, IRFunType tb1 tb2) ->
            whenListTEq ta1 tb1 $ \ta1' tb1' ->
                whenTEq ta2 tb2 $ \ta2' tb2' ->
                    f (setType v1 (IRFunType ta1' ta2')) (setType v2 (IRFunType tb1' tb2'))
        (ta, tb) -> fail $ 
            "Unexpected Type mismatch: " <>
            show ta <> " /= " <> show tb <> "\n" <> stackTrace

whenListTEq :: (HasCallStack, MonadFail m, Typeable v1, Typeable v2) =>
                HList v1 xs -> HList v2 ys -> (HList v1 xs -> HList v2 xs -> m c) -> m c
whenListTEq HNil HNil f = f HNil HNil
whenListTEq (x :+: xs) (y :+: ys) f =
    whenTEq x y $ \x' y' -> do
        whenListTEq xs ys $ \xs' ys' ->
            f (x' :+: xs') (y' :+: ys')
whenListTEq ta tb _ = fail $
    "Unexpected type list mismatch: " <>
    show (hListLength ta) <> " /= " <> show (hListLength tb) <>
    "\n" <> stackTrace

whenListElemTEq :: (HasCallStack, MonadFail m, Typeable v1, Typeable v2) => 
                  v1 (Ptr [a]) -> v2 b -> (v1 (Ptr [a]) -> v2 a -> m c) -> m c
whenListElemTEq v1 v2 f = 
    whenTEq (getType v1) (IRListType (getType v2)) $
        \ta' (IRListType tb') -> f (setType v1 ta') (setType v2 tb') 

whenPtrTEq :: (HasCallStack, MonadFail m, Typeable v1, Typeable v2) => 
                  v1 (Ptr a) -> v2 b -> (v1 (Ptr a) -> v2 a -> m c) -> m c
whenPtrTEq v1 v2 f = 
    whenTEq (getType v1) (IRPtrType (getType v2)) $
        \ta' (IRPtrType tb') -> f (setType v1 ta') (setType v2 tb') 

whenFunTEq :: (HasCallStack, MonadFail m, Typeable v) =>
              IRFunDecl as1 r1 ->
              v (Ptr (as2 --> r2)) ->
              (IRFunDecl as2 r2 -> m c)
              -> m c
whenFunTEq (IRFunDecl label funArgs funRet) t f =
    case getType t of
        IRFunType argT retT ->
            whenListTEq (hListZip2 (\t' (Var id _ k) -> Var id t' k) (flip (Var "") Temp) argT funArgs) funArgs $
                \funArgs' _ ->
                    whenTEq retT funRet $ \retT' _ -> f $ IRFunDecl label funArgs' retT'
        _ -> coreError

ifFunTypeEq :: forall as1 r1 as2 r2 c v. Typeable v =>
               IRFunDecl as1 r1 ->
               v (Ptr (as2 --> r2)) ->
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

toCastable :: forall m a b. (MonadFail m, HasCallStack) => IRType a -> IRType b -> m (Constrained2 Castable IRType a b)
toCastable IRBoolType IRIntType = pure (Constrained2 IRBoolType IRIntType)
toCastable IRCharType IRIntType = pure (Constrained2 IRCharType IRIntType)
toCastable t u@IRUnknownType{} = pure (Constrained2 t u)
toCastable u@IRUnknownType{} t = pure (Constrained2 u t)
toCastable (IRPtrType t1) (IRPtrType t2) = do
    Constrained2 t1' t2' <- toCastable t1 t2
    pure $ Constrained2 (IRPtrType t1') (IRPtrType t2')
toCastable (IRListType t1) (IRListType t2) = do
    Constrained2 t1' t2' <- toCastable t1 t2
    pure $ Constrained2 (IRListType t1') (IRListType t2')
toCastable (IRTupleType a1 b1) (IRTupleType a2 b2) = do
    Constrained2 a1' a2' <- toCastable a1 a2
    Constrained2 b1' b2' <- toCastable b1 b2
    pure $ Constrained2 (IRTupleType a1' b1') (IRTupleType a2' b2')
toCastable (IRFunType as1 r1) (IRFunType as2 r2) = do
    Constrained2 as1' as2' <- castHList as1 as2    
    Constrained2 r1' r2' <- toCastable r1 r2
    pure $ Constrained2 (IRFunType as1' r1') (IRFunType as2' r2')

    where
        castHList :: HList IRType xs -> HList IRType ys -> m (Constrained2 Castable (HList IRType) xs ys)
        castHList HNil HNil = pure (Constrained2 HNil HNil)
        castHList HNil (y :+: ys) = fail "Cannot generate castable constraint for fun type. Argument mismatch"
        castHList (x :+: xs) HNil = fail "Cannot generate castable constraint for fun type. Argument mismatch"
        castHList (x :+: xs) (y :+: ys) = do 
            Constrained2 x' y' <- toCastable x y
            Constrained2 xs' ys' <- castHList xs ys
            pure (Constrained2 (x' :+: xs') (y' :+: ys'))

toCastable t1 t2 = fail $
    "Cannot generate castable constraint for these types: " <> show t1 <> " " <> show t2
    
castFunArgs :: HList Var xs -> [Some1 Value] -> IRMonad (HList Value xs)
castFunArgs HNil [] = pure HNil
castFunArgs (arg :+: args) (Some1 concreteArg:concreteArgs) = do
    concreteArg' <- cast concreteArg (getType arg) 
    concreteArgs' <- castFunArgs args concreteArgs
    return (concreteArg' :+: concreteArgs')
castFunArgs hs ys = coreErrorWithDesc . T.pack $
    "Mismatched number of function arguments: " <>
    show (hListLength hs) <> " /= " <> show (length ys)

showVarList :: [Some1 Var] -> String
showVarList = concatMap (\(Some1 v) -> show v <> " ")

callFunWith :: Identifier -> [Some1 Value] -> IRMonad (Some1 Var)
callFunWith funName args = do
    Some1 (IRFunDecl' fun) <- findFunByName funName
    args' <- castFunArgs (fun ^. funArgs) args
    dst <- mkTmpVar (fun ^. funRetType)
    body <>= [ Call dst (IRLit $ IRFun fun) args' ]
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
findVarByName id = findVarByPred (\(Var varId _ _) -> varId == id)

getVoidVar :: IRMonad (Var Unit)
getVoidVar = findVar (== "0void_var") IRVoidType

findVar :: forall a. (Identifier -> Bool) -> IRType a -> IRMonad (Var a)
findVar f reqT = do
    Some1 varCtx <- use vars
    findVar' varCtx
    where
        findVar' :: HList Var xs -> IRMonad (Var a)
        findVar' HNil = coreError
        findVar' (v@(Var varId varT k) :+: rest)
            | f varId = do
                ifIRTypeEq reqT varT (\reqT' varT' -> return (Var varId varT' k))
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
                TCT.TPrint _ -> findVarByPred $ \(Var id varT _) ->
                    ifIRTypeEq tconT varT (\_ _ -> T.isPrefixOf "0print_con" id) (const False)
                TCT.TEq _ -> findVarByPred $ \(Var id varT _) ->
                    ifIRTypeEq tconT varT (\_ _ -> T.isPrefixOf "0eq_con" id) (const False)
                TCT.TOrd _ -> findVarByPred $ \(Var id varT _) ->
                    ifIRTypeEq tconT varT (\_ _ -> T.isPrefixOf "0ord_con" id) (const False)

declareBodyAs :: IRMonad () -> IRMonad [IRInstr]
declareBodyAs st = do
    body .= []
    st
    result <- use body
    body .= []
    return result

