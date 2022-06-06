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
    |   TLt EntityLoc TypeVar
    |   TLe EntityLoc TypeVar
    |   TGt EntityLoc TypeVar
    |   TGe EntityLoc TypeVar
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
unTCon (TLt _ t) = t
unTCon (TLe _ t) = t
unTCon (TGt _ t) = t
unTCon (TGe _ t) = t
unTCon (TPrint _ t) = t

type TConConstructor = EntityLoc -> TypeVar -> TCon

constructTConFrom :: TCon -> TConConstructor
constructTConFrom TEq{} = TEq
constructTConFrom TLt{} = TLt
constructTConFrom TLe{} = TLe
constructTConFrom TGt{} = TGt
constructTConFrom TGe{} = TGe
constructTConFrom TPrint{} = TPrint

areTConSameKind :: TCon -> TCon -> Bool
areTConSameKind TEq{} TEq{} = True
areTConSameKind TLt{} TLt{} = True
areTConSameKind TLe{} TLe{} = True
areTConSameKind TGt{} TGt{} = True
areTConSameKind TGe{} TGe{} = True
areTConSameKind TPrint{} TPrint{} = True
areTConSameKind _ _ = False

mkArg :: TCon -> CoreIdentifier
mkArg (TEq l t) = CoreIdentifier l ("_teq_" <> t)
mkArg (TLt l t) = CoreIdentifier l ("_tlt_" <> t)
mkArg (TLe l t) = CoreIdentifier l ("_tle_" <> t)
mkArg (TGt l t) = CoreIdentifier l ("_tgt_" <> t)
mkArg (TGe l t) = CoreIdentifier l ("_tge_" <> t)
mkArg (TPrint l t) = CoreIdentifier l ("_tprint_" <> t)

mkTConType :: TCon -> CoreType -> CoreType
mkTConType tcon argType =
    let loc = getLoc tcon
    in case tcon of
            TPrint{} -> CoreFunType loc (Just argType) (CoreVoidType loc)
            _ -> CoreFunType loc (Just argType) (CoreFunType loc (Just argType) (CoreBoolType loc))

mkTConVarType :: TCon -> CoreType
mkTConVarType tcon = mkTConType tcon $ CoreVarType (getLoc tcon) (unTCon tcon)

mkTConName :: TCon -> CoreType -> Text
mkTConName tcon typ =
    let prefix =
            case tcon of
                TEq{} -> "eq"
                TLt{} -> "lt"
                TLe{} -> "le"
                TGt{} -> "gt"
                TGe{} -> "ge"
                TPrint{} -> "print"
        suffix =
            case typ of
                CoreIntType{} -> "int"
                CoreBoolType{} -> "bool"
                CoreCharType{} -> "char"
                CoreVoidType{} -> "void"
                CoreListType{} -> "list"
                CoreTupleType{} -> "tup"
                _ -> error $ "no overloaded instance exists for: " <> show typ
    in "_" <> prefix <> "_" <> suffix


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
        ambiguousTConErr tcon >>= throwErr

ambiguousTConErr :: TCon -> TConMonad Error
ambiguousTConErr tcon = do
    let header = T.pack $ "Unable to resolve ambiguous instance: " <> show tcon
    err <- definition (T.pack $ "'" <>
                       show tcon <>
                       "' instance has been inferred for: ") tcon
    return $ header : err

noArgFunTConErr :: TCon -> TConMonad ()
noArgFunTConErr tcon = err >>= throwErr
    where 
        err = do
            let header = T.unlines [
                    "Unable to create constraint " <> T.pack (show tcon),
                    "Enclosing function takes no arguments"]
            err <- definition (T.pack $ "'" <>
                               show tcon <>
                               "' instance has been inferred for: ") tcon
            return $ header : err


instance Eq TCon where
    t1 == t2 = areTConSameKind t1 t2 && unTCon t1 == unTCon t2

instance Hashable TCon where
    hashWithSalt seed (TEq _ t) = hashWithSalt (hashWithSalt seed t) (1 :: Int)
    hashWithSalt seed (TLt _ t) = hashWithSalt (hashWithSalt seed t) (2 :: Int)
    hashWithSalt seed (TLe _ t) = hashWithSalt (hashWithSalt seed t) (3 :: Int)
    hashWithSalt seed (TGt _ t) = hashWithSalt (hashWithSalt seed t) (4 :: Int)
    hashWithSalt seed (TGe _ t) = hashWithSalt (hashWithSalt seed t) (5 :: Int)
    hashWithSalt seed (TPrint _ t) = hashWithSalt (hashWithSalt seed t) (6 :: Int)

instance Ord TCon where
    compare x y = compare (hash x) (hash y)

instance Show TCon where
    show (TEq _ t) = "Equal " <> show t
    show (TLt _ t) = "LessThan " <> show t
    show (TLe _ t) = "LessEqual " <> show t
    show (TGt _ t) = "GreaterThan " <> show t
    show (TGe _ t) = "GreaterEqual " <> show t
    show (TPrint _ t) = "Printable " <> show t

instance Locatable TCon where
    setLoc l (TEq _ t) = TEq l t
    setLoc l (TLt _ t) = TLt l t
    setLoc l (TLe _ t) = TLe l t
    setLoc l (TGt _ t) = TGt l t
    setLoc l (TGe _ t) = TGe l t
    setLoc l (TPrint _ t) = TPrint l t
    getLoc (TEq l t) = l
    getLoc (TLt l t) = l
    getLoc (TLe l t) = l
    getLoc (TGt l t) = l
    getLoc (TGe l t) = l
    getLoc (TPrint l t) = l
