{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SPL.Compiler.TypeChecker.Unify where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad
import Control.Monad.Random
import System.Random
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.TCTEntityLocation
import SPL.Compiler.Common.EntityLocation

type Error = [Text]

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
    s $* (TCTListType e a) = rank1Norm $ TCTListType e (s $* a)
    s $* (TCTTupleType e a b) = rank1Norm $ TCTTupleType e (s $* a) (s $* b)
    s $* (TCTFunType d e a b) = rank1Norm $ TCTFunType d e (s $* a) (s $* b)
    s $* (TCTUniversalType l tv t) =
        let t' = s $* t
            boundVars = typeVars t' `S.intersection` tv
        in rank1Norm $ generalise boundVars t'

instance SubstApply (Map Text TCTType) where
    s $* c = ($*) s <$> c

typeVars :: TCTType -> Set TypeVar
typeVars (TCTVarType _ a) = S.singleton a
typeVars (TCTFunType _ _ a b) = typeVars a <> typeVars b
typeVars (TCTTupleType _ a b) = typeVars a <> typeVars b
typeVars (TCTListType _ a) = typeVars a
typeVars _ = S.empty

boundTypeVars :: TCTType -> Set TypeVar
boundTypeVars (TCTUniversalType _ tv a) = tv <> boundTypeVars a
boundTypeVars (TCTFunType _ _ a b) = boundTypeVars a <> boundTypeVars b
boundTypeVars (TCTTupleType _ a b) = boundTypeVars a <> boundTypeVars b
boundTypeVars (TCTListType _ a) = boundTypeVars a
boundTypeVars _ = S.empty

freeTypeVars :: TCTType -> Set TypeVar
freeTypeVars t = typeVars t `S.difference` boundTypeVars t

sanitize :: StdGen -> TCTType -> Subst -> Subst
sanitize g t s =
    case t of
        (TCTFunType _ _ a b) -> 
            let (g', g'') = split g 
                s' = sanitize g' a s 
            in sanitize g'' b s'
        (TCTTupleType _ a b) -> 
            let (g', g'') = split g 
                s' = sanitize g' a s 
            in sanitize g'' b s'
        (TCTListType _ a) -> sanitize g a s
        (TCTUniversalType _ tv a) -> evalRand (foldM foldRename s tv) g
        _ -> s
    where
        foldRename :: Subst -> TypeVar -> Rand StdGen Subst
        foldRename (Subst subst) v = do
            suffix <- T.pack . show <$> getRandomR (10000 :: Int, 90000)
            return . Subst $ rename v (v <> suffix) <$> subst

        rename :: TypeVar -> TypeVar -> TCTType -> TCTType
        rename from to v@(TCTVarType l a)
            | from == a = TCTVarType l to
            | otherwise = v
        rename from to (TCTUniversalType l tv a) =
            TCTUniversalType l
                             (S.map (\v -> if v == from then to else v) tv)
                             (rename from to a)
        rename from to (TCTFunType l c a b) =
            TCTFunType l c (rename from to a) (rename from to b)
        rename from to (TCTTupleType l a b) =
            TCTTupleType l (rename from to a) (rename from to b)
        rename from to (TCTListType l a ) =
            TCTListType l (rename from to a)
        rename from to t = t

rank1Norm :: TCTType -> TCTType
rank1Norm t = generalise (boundTypeVars t) $ removeQuantifiers t
    where
        removeQuantifiers (TCTUniversalType _ _ a) = a
        removeQuantifiers (TCTFunType c l a b) =
            TCTFunType c l (removeQuantifiers a) (removeQuantifiers b)
        removeQuantifiers (TCTTupleType l a b) =
            TCTTupleType l (removeQuantifiers a) (removeQuantifiers b)
        removeQuantifiers (TCTListType l a) = TCTListType l $ removeQuantifiers a
        removeQuantifiers a = a

generalise :: Set TypeVar -> TCTType -> TCTType
generalise boundVars (TCTUniversalType l bs t) =
    TCTUniversalType l (bs <> (typeVars t `S.intersection` boundVars)) t
generalise boundVars t =
    let boundVarsInT = typeVars t `S.intersection` boundVars
     in if not (null boundVarsInT) then
            TCTUniversalType (getLoc t) boundVarsInT t
        else
            t

occurs :: TypeVar -> TCTType -> Bool
occurs var t = S.member var (typeVars t)
occursError :: TypeVar -> TCTType -> Error
occursError var t =
    ["Occurs check: cannot construct the infinite type: "
        <> var
        <> " ~ "
        <> T.pack (show t)]

unify :: TCTType -> TCTType -> Either Error Subst
unify t1 t2 = do
    Subst subst <- unifyHelper mempty t1 t2
    let boundVars = boundTypeVars t1 <> boundTypeVars t2
    return . Subst $ rank1Norm . generalise boundVars <$> subst

    where
        typeMismatchError t1 t2 =
            ["Couldn't match type '" <> T.pack (show t1)
                                     <> "' with '"
                                     <> T.pack (show t2)
                                     <> "'"]
        unifyHelper :: Set TypeVar -> TCTType -> TCTType -> Either Error Subst
        unifyHelper boundVars (TCTUniversalType _ tv t1) t2 = do
            unifyHelper (boundVars <> tv) t1 t2
        unifyHelper boundVars t1 (TCTUniversalType _ tv t2) = do
            unifyHelper (boundVars <> tv) t1 t2

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

        unifyHelper boundVars (TCTListType _ a) (TCTListType _ b) =
            unifyHelper boundVars a b

        unifyHelper boundVars (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = do
            subst1 <- unifyHelper boundVars a1 a2
            subst2 <- unifyHelper boundVars (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1

        unifyHelper boundVars (TCTFunType _ _ a1 b1) (TCTFunType _ _ a2 b2) = do
            subst1 <- unifyHelper boundVars a1 a2
            subst2 <- unifyHelper boundVars (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1

        unifyHelper _ t1 t2 = Left $ typeMismatchError t1 t2
