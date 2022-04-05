{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module SPL.Compiler.TypeChecker.Unify where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.TCTEntityLocation
import SPL.Compiler.Common.EntityLocation

type Error = Text

newtype Subst = Subst (Map TypeVar TCTType) deriving (Eq, Show)

class SubstApply a where
    ($*) :: Subst -> a -> a

infixr 1 $*

instance Semigroup Subst where
    -- `(subst2 <> subst1) t` means 
    -- first apply `subst1` to `t` and then apply `subst2` on result
    -- Note that order of application matters, e.g.:
    -- subst2 = [a |-> Int] , 
    -- subst1 = [b |-> (a -> Int)]
    -- subst1(subst2(b -> b)) = (Int -> Int) -> (Int -> Int)
    -- subst1(subst1(b -> b)) = (a -> Int) -> (a -> Int)
    subst2@(Subst a) <> (Subst b) = Subst (M.unionWith (\_ b -> b) a (($*) subst2 <$> b))

instance Monoid Subst where
    mempty = Subst mempty 
    mappend = (<>)

instance SubstApply TCTType where 
    _ $* (TCTIntType e) = TCTIntType e
    _ $* (TCTCharType e) = TCTCharType e
    _ $* (TCTBoolType e) = TCTBoolType e
    _ $* (TCTVoidType e) = TCTVoidType e
    (Subst s) $* v@(TCTVarType l a) = setLoc l (M.findWithDefault v a s)
    s $* (TCTListType e a) = TCTListType e (s $* a)
    s $* (TCTTupleType e a b) = TCTTupleType e (s $* a) (s $* b)
    s $* (TCTFunType d e a b) = TCTFunType d e (s $* a) (s $* b)
    s $* (TCTUniversalType _ _ t) = s $* t

instance SubstApply (Map Text TCTType) where
    s $* c = ($*) s <$> c

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
unify t1 t2 = unifyHelper mempty t1 t2
    where
        typeMismatchError t1 t2 =
            "Couldn't match type '" <> T.pack (show t1) 
                                    <> "' with '" 
                                    <> T.pack (show t2)
                                    <> "'"
        unifyHelper :: Set TypeVar -> TCTType -> TCTType -> Either Error Subst
        unifyHelper boundVars (TCTUniversalType _ fv t1) t2 = do
            unifyHelper (boundVars <> fv) t1 t2
        unifyHelper boundVars t1 (TCTUniversalType _ fv t2) = do
            unifyHelper (boundVars <> fv) t1 t2
        unifyHelper _ (TCTIntType _) (TCTIntType _) = Right mempty
        unifyHelper _ (TCTCharType _) (TCTCharType _) = Right mempty
        unifyHelper _ (TCTBoolType _) (TCTBoolType _) = Right mempty
        unifyHelper _ (TCTVoidType _) (TCTVoidType _) = Right mempty
        unifyHelper boundVars v1@(TCTVarType _ a) v2@(TCTVarType _ b)
            | a == b = Right mempty
            | S.member a boundVars = Right . Subst $ M.singleton a v2
            | S.member b boundVars = Right . Subst $ M.singleton b v2
            | otherwise = Left $ typeMismatchError v1 v2
        unifyHelper boundVars v@(TCTVarType _ a) t = do
            unless (S.member a boundVars) $
                Left $ typeMismatchError v t
            if not $ occurs a t then
                Right . Subst $ M.singleton a t
            else
                Left $ occursError a t
        unifyHelper boundVars t v@(TCTVarType _ a) = do
            unless (S.member a boundVars) $
                Left $ typeMismatchError v t
            if not $ occurs a t then
                Right . Subst $ M.singleton a t
            else
                Left $ occursError a t
        unifyHelper boundVars (TCTListType _ a) (TCTListType _ b) = unifyHelper boundVars a b
        unifyHelper boundVars (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = do
            subst1 <- unifyHelper boundVars a1 a2 
            subst2 <- unifyHelper boundVars (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1
        unifyHelper boundVars (TCTFunType _ _ a1 b1) (TCTFunType _ _ a2 b2) = do
            subst1 <- unifyHelper boundVars a1 a2 
            subst2 <- unifyHelper boundVars (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1
        unifyHelper _ t1 t2 = Left $ typeMismatchError t1 t2

-- check if `t` a instance of `mgt` 
-- --note that type variables of different names are not equivalent--
-- and if so return their substitution
getMGTInstance :: TCTType -> TCTType -> Either Text Subst
getMGTInstance t mgt = do
    Subst subst <- unify t mgt
    let tvVars = typeVars t
    forM_ tvVars $ \v ->
        case M.lookup v subst of
            Just t -> Left $
                "unexpected type " <> 
                T.pack (show v) <>
                "expected type " <> 
                T.pack (show t)
            Nothing -> return ()
    return (Subst subst)
