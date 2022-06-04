{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module SPL.Compiler.SemanticAnalysis.OverloadLib where

import SPL.Compiler.Common.Error
import Data.Maybe (fromMaybe)
import Control.Lens
import Control.Monad.State
import Data.Hashable
import Data.Set (Set)
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Set as S
import Data.Foldable (toList)

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.Unify
import SPL.Compiler.SemanticAnalysis.CoreEntityLocation
import Control.Monad.Extra (unlessM)

data TCon =
        TEq EntityLoc TypeVar
    |   TOrd EntityLoc TypeVar
    |   TPrint EntityLoc TypeVar

data TConState = TConState {
    _env :: Map Text ([TCon], CoreType),
    _newTCon :: Set TCon,
    _tconArgs :: Map TCon CoreIdentifier,
    _getSourcePathTCon :: FilePath,
    _getSourceCodeTCon :: [Text]
}

makeLenses 'TConState

instance ContainsSource TConState where
    getFilePath = _getSourcePathTCon
    getSource = _getSourceCodeTCon

type TConMonad a = StateT TConState (Either Error) a

unTCon :: TCon -> TypeVar
unTCon (TEq _ t) = t
unTCon (TOrd _ t) = t
unTCon (TPrint _ t) = t

type TConConstructor = EntityLoc -> TypeVar -> TCon

constructTConFrom :: TCon -> TConConstructor
constructTConFrom (TEq _ _) = TEq
constructTConFrom (TOrd _ _) = TOrd
constructTConFrom (TPrint _ _) = TPrint

areTConSameKind :: TCon -> TCon -> Bool
areTConSameKind (TEq _ _) (TEq _ _) = True
areTConSameKind (TOrd _ _) (TOrd _ _) = True
areTConSameKind (TPrint _ _) (TPrint _ _) = True
areTConSameKind _ _ = False

mkArg :: TCon -> CoreIdentifier
mkArg (TEq l t) = CoreIdentifier l ("_teq_" <> t)
mkArg (TOrd l t) = CoreIdentifier l ("_tord_" <> t)
mkArg (TPrint l t) = CoreIdentifier l ("_tprint_" <> t)

mkTConType :: TCon -> CoreType -> CoreType
mkTConType (TEq l _) argType =
    CoreFunType l (Just argType) (CoreFunType l (Just argType) (CoreBoolType l))
mkTConType (TOrd l _) argType =
    CoreFunType l (Just argType) (CoreFunType l (Just argType) (CoreBoolType l))
mkTConType (TPrint l _) argType =
    CoreFunType l (Just argType) (CoreVoidType l)

mkTConVarType :: TCon -> CoreType
mkTConVarType tcon = mkTConType tcon $ CoreVarType (getLoc tcon) (unTCon tcon)

mkTConName :: TCon -> CoreType -> Text
mkTConName TEq{} CoreIntType{} = "_eq_int"
mkTConName TEq{} CoreBoolType{} = "_eq_bool"
mkTConName TEq{} CoreCharType{} = "_eq_char"
mkTConName TEq{} CoreVoidType{} = "_eq_void"
mkTConName TEq{} CoreListType{} = "_eq_list"
mkTConName TEq{} CoreTupleType{} = "_eq_tup"
mkTConName TOrd{} CoreIntType{} = "_ord_int"
mkTConName TOrd{} CoreBoolType{} = "_ord_bool"
mkTConName TOrd{} CoreCharType{} = "_ord_char"
mkTConName TOrd{} CoreVoidType{} = "_ord_void"
mkTConName TOrd{} CoreListType{} = "_ord_list"
mkTConName TOrd{} CoreTupleType{} = "_ord_tup"
mkTConName TPrint{} CoreIntType{} = "_print_int"
mkTConName TPrint{} CoreBoolType{} = "_print_bool"
mkTConName TPrint{} CoreCharType{} = "_print_char"
mkTConName TPrint{} CoreVoidType{} = "_print_void"
mkTConName TPrint{} (CoreListType _ CoreCharType{}) = "_print_char_list"
mkTConName TPrint{} CoreListType{} = "_print_list"
mkTConName TPrint{} CoreTupleType{} = "_print_tup"
mkTConName _ t = error $ "no overloaded instance exists for: " <> show t

-- given a TEQ/TORD/TPrint and the type t we want to TEQ/TORD/TPRINT
-- we need to generate the expression which is a (partially) applied
-- function that takes the t and EQs/ORDs/PRINTs it
-- We also need to return the type of the resulting expression as
-- we would pass it into an overloaded function call thus we need to
-- change its type there
mkTConArgExpr :: (TCon, CoreType) -> TConMonad (CoreExpr, CoreType)
mkTConArgExpr (c, t@CoreIntType{}) =
    let typ = mkTConType c t
    in pure (FunIdentifierExpr typ (CoreIdentifier (getLoc c) (mkTConName c t)), typ)
mkTConArgExpr (c, t@CoreBoolType{}) =
    let typ = mkTConType c t
    in pure (FunIdentifierExpr typ (CoreIdentifier (getLoc c) (mkTConName c t)), typ)
mkTConArgExpr (c, t@CoreCharType{}) =
    let typ = mkTConType c t
    in pure (FunIdentifierExpr typ (CoreIdentifier (getLoc c) (mkTConName c t)), typ)
mkTConArgExpr (c, t@CoreVoidType{}) =
    let typ = mkTConType c t
    in pure (FunIdentifierExpr typ (CoreIdentifier (getLoc c) (mkTConName c t)), typ)
mkTConArgExpr (c, t@(CoreVarType _ v)) = do
    let tcon = constructTConFrom c (getLoc c) v
    maybeArg <- M.lookup tcon <$> use tconArgs
    case maybeArg of
        Nothing -> error $ "internal error: overloaded argument not found: " <> show c
        Just tconLocalArg -> do
            let typ = mkTConType c t
            pure (VarIdentifierExpr tconLocalArg, typ)
mkTConArgExpr (c@TPrint{}, t@(CoreListType loc (CoreCharType _))) =
    let typ = mkTConType c t
    in pure (FunIdentifierExpr typ (CoreIdentifier (getLoc c) (mkTConName c t)), typ)
mkTConArgExpr (c, t@(CoreListType loc elemT)) = do
    (baseExpr, baseTyp) <- mkTConArgExpr (c, elemT)
    let typ = mkTConType c t
        callerTyp = CoreFunType loc (pure baseTyp) typ
        caller = FunIdentifierExpr callerTyp $ CoreIdentifier (getLoc c) (mkTConName c t)
    pure (FunCallExpr (CoreFunCall loc caller callerTyp [baseExpr]), typ)
mkTConArgExpr (c, t@(CoreTupleType loc elemT1 elemT2)) = do
    (baseExpr1, baseTyp1) <- mkTConArgExpr (c, elemT1)
    (baseExpr2, baseTyp2) <- mkTConArgExpr (c, elemT2)
    let typ = mkTConType c t
        callerTyp = foldr (CoreFunType loc . pure) typ [baseTyp1, baseTyp2]
        caller = FunIdentifierExpr callerTyp $ CoreIdentifier (getLoc c) (mkTConName c t)
    pure (FunCallExpr (CoreFunCall loc caller callerTyp [baseExpr1, baseExpr2]), typ)
mkTConArgExpr _ = undefined

ambiguousTConCheck :: CoreType -> TCon -> TConMonad ()
ambiguousTConCheck t tcon = do
    let freeTV = freeVars t
        tv = unTCon tcon
    unless (tv `S.member` freeTV) $
        tconError tcon >>= throwErr

tconError :: TCon -> TConMonad Error
tconError tcon = do
    let header = T.pack $ "Unable to resolve ambiguous instance: " <> show tcon
    err <- definition (T.pack $ "'" <>
                       show tcon <>
                       "' instance has been inferred for: ") tcon
    return $ header : err

instance Eq TCon where
    t1 == t2 = areTConSameKind t1 t2 && unTCon t1 == unTCon t2

instance Hashable TCon where
    hashWithSalt seed (TEq _ t) = hashWithSalt (hashWithSalt seed t) (1 :: Int)
    hashWithSalt seed (TOrd _ t) = hashWithSalt (hashWithSalt seed t) (2 :: Int)
    hashWithSalt seed (TPrint _ t) = hashWithSalt (hashWithSalt seed t) (3 :: Int)

instance Ord TCon where
    compare x y = compare (hash x) (hash y)

instance Show TCon where
    show (TEq _ t) = "Equality " <> show t
    show (TOrd _ t) = "Ordered " <> show t
    show (TPrint _ t) = "Printable " <> show t

instance Locatable TCon where
    setLoc l (TEq _ t) = TEq l t
    setLoc l (TOrd _ t) = TOrd l t
    setLoc l (TPrint _ t) = TPrint l t
    getLoc (TEq l t) = l
    getLoc (TOrd l t) = l
    getLoc (TPrint l t) = l

