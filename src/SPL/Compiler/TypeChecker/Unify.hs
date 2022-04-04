{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.TypeChecker.Unify where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.TCTEntityLocation
import SPL.Compiler.Common.EntityLocation

type Error = Text

newtype Subst = Subst (Map TypeVar TCTType) deriving (Eq, Show)

instance Semigroup Subst where
    -- `(subst2 <> subst1) t` means 
    -- first apply `subst1` to `t` and then apply `subst2` on result
    -- Note that order of application matters, e.g.:
    -- subst2 = [a |-> Int] , 
    -- subst1 = [b |-> (a -> Int)]
    -- subst1(subst2(b -> b)) = (Int -> Int) -> (Int -> Int)
    -- subst1(subst1(b -> b)) = (a -> Int) -> (a -> Int)
    subst2@(Subst a) <> (Subst b) = Subst (M.unionWith (\_ b -> b) a (substApply subst2 <$> b))

instance Monoid Subst where
    mempty = Subst mempty 
    mappend = (<>)

substApply :: Subst -> TCTType -> TCTType
substApply _ (TCTIntType e) = TCTIntType e
substApply _ (TCTCharType e) = TCTCharType e
substApply _ (TCTBoolType e) = TCTBoolType e
substApply _ (TCTVoidType e) = TCTVoidType e
substApply (Subst s) v@(TCTVarType l a) = setLoc l (M.findWithDefault v a s)
substApply s (TCTListType e a) = TCTListType e (substApply s a)
substApply s (TCTTupleType e a b) = TCTTupleType e (substApply s a) (substApply s b)
substApply s (TCTFunType d e a b) = TCTFunType d e (substApply s a) (substApply s b)

typeVars :: TCTType -> Set TypeVar
typeVars (TCTVarType _ a) = S.singleton a
typeVars (TCTFunType _ _ a b) = typeVars a <> typeVars b
typeVars (TCTTupleType _ a b) = typeVars a <> typeVars b
typeVars (TCTListType _ a) = typeVars a
typeVars _ = S.empty

occurs :: TypeVar -> TCTType -> Bool
occurs var t = S.member var (typeVars t)
occursError :: TypeVar -> TCTType -> Error
occursError var t =
    "Occurs check: cannot construct the infinite type: "
        <> var 
        <> " ~ " 
        <> T.pack (show t)

unify :: TCTType -> TCTType -> Either Error Subst
unify (TCTIntType _) (TCTIntType _) = Right mempty
unify (TCTCharType _) (TCTCharType _) = Right mempty
unify (TCTBoolType _) (TCTBoolType _) = Right mempty
unify (TCTVoidType _) (TCTVoidType _) = Right mempty
unify (TCTVarType _ a) v2@(TCTVarType _ b)
    | a == b = Right mempty
    | otherwise = Right . Subst $ M.singleton a v2
unify (TCTVarType _ a) t =
    if not $ occurs a t then
        Right . Subst $ M.singleton a t
    else
        Left $ occursError a t
unify t (TCTVarType _ a) =
    if not $ occurs a t then
        Right . Subst $ M.singleton a t
    else
        Left $ occursError a t
unify (TCTListType _ a) (TCTListType _ b) = unify a b
unify (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = do
    subst1 <- unify a1 a2 
    subst2 <- unify (substApply subst1 b1) (substApply subst1 b2)
    return $ subst2 <> subst1
unify (TCTFunType _ _ a1 b1) (TCTFunType _ _ a2 b2) = do
    subst1 <- unify a1 a2 
    subst2 <- unify (substApply subst1 b1) (substApply subst1 b2)
    return $ subst2 <> subst1
unify t1 t2 = Left $ 
    "Couldn't match type '" <> T.pack (show t1) 
                            <> "' with '" 
                            <> T.pack (show t2)
                            <> "'"
