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

class Types a where
    ($*) :: Subst -> a -> a
    freeVars :: a -> Set TypeVar

infixr 1 $*

instance Semigroup Subst where
    -- `(s1 <> s2) t` means 
    -- first apply `s2` to `t` and then apply `s1` on result
    -- Note that order of application matters, e.g.:
    -- s2 = [a |-> Int] , 
    -- s1 = [b |-> (a -> Int)]
    -- s1(s2(b -> b)) = (Int -> Int) -> (Int -> Int)
    -- s2(s1(b -> b)) = (a -> Int) -> (a -> Int)
    s1@(Subst s1') <> (Subst s2') = Subst ( (($*) s1 <$> s2') `M.union` s1')

instance Monoid Subst where
    mempty = Subst mempty
    mappend = (<>)

instance Types TCTType where
    s $* (TCTIntType e) = TCTIntType e
    s $* (TCTCharType e) = TCTCharType e
    s $* (TCTBoolType e) = TCTBoolType e
    s $* (TCTVoidType e) = TCTVoidType e
    (Subst s) $* v@(TCTVarType l a) = setLoc l (M.findWithDefault v a s)
    s $* (TCTListType e a) = TCTListType e (s $* a)
    s $* (TCTTupleType e a b) = TCTTupleType e (s $* a) (s $* b)
    s $* (TCTFunType d e a b) = TCTFunType d e (s $* a) (s $* b)
    freeVars v@(TCTVarType l a) = S.singleton a
    freeVars (TCTListType _ a) = freeVars a
    freeVars (TCTTupleType _ a b) = freeVars a <> freeVars b
    freeVars (TCTFunType _ _ a b) = freeVars a <> freeVars b
    freeVars _ = mempty

instance Types Scheme where
    (Subst s) $* (Scheme tv t) = Scheme tv $ Subst (foldr M.delete s tv) $* t
    freeVars (Scheme tv t) = freeVars t `S.difference` tv

instance Types TypeEnv where
    s $* (TypeEnv env) = TypeEnv $ ($*) s <$> env
    freeVars (TypeEnv env) = foldMap freeVars $ M.elems env

instance Types TCT where
    s $* (TCT leaves) = TCT $ map (s $*) leaves
    freeVars _ = undefined

instance Types TCTLeaf where
    s $* (TCTVar varDecl) = TCTVar $ s $* varDecl
    s $* (TCTFun funDecl) = TCTFun $ s $* funDecl
    freeVars _ = undefined

instance Types TCTVarDecl where
    s $* (TCTVarDecl loc t id expr) = TCTVarDecl loc (s $* t) id expr
    freeVars _ = undefined

instance Types TCTFunDecl where
    s $* (TCTFunDecl loc id args t body) = TCTFunDecl loc id args (s $* t) (s $* body)
    freeVars _ = undefined

instance Types TCTFunBody where
    s $* (TCTFunBody loc varDecls stmts) = TCTFunBody loc (map (s $*) varDecls) stmts
    freeVars _ = undefined

generalise :: TypeEnv -> TCTType -> Scheme
generalise env t = Scheme (freeVars t `S.difference` freeVars env) t

liftToScheme :: TCTType -> Scheme
liftToScheme = Scheme mempty


typeMismatchError t1 t2 =
    ["Couldn't match type '" <> T.pack (show t1)
                             <> "' with '"
                             <> T.pack (show t2)
                             <> "'"]

occurs :: TypeVar -> TCTType -> Bool
occurs var t = S.member var (freeVars t)
occursError :: TypeVar -> TCTType -> Error
occursError var t =
    ["Occurs check: cannot construct the infinite type: "
        <> var
        <> " ~ "
        <> T.pack (show t)]

unify :: TCTType -> TCTType -> Either Error Subst
unify t1 t2 = unify' t1 t2
    where
        unify' :: TCTType -> TCTType -> Either Error Subst
        unify' (TCTIntType _) (TCTIntType _) = Right mempty
        unify' (TCTCharType _) (TCTCharType _) = Right mempty
        unify' (TCTBoolType _) (TCTBoolType _) = Right mempty
        unify' (TCTVoidType _) (TCTVoidType _) = Right mempty

        unify' v1@(TCTVarType _ a) v2@(TCTVarType _ b)
            | a == b = Right mempty
            | otherwise = Right . Subst $ M.singleton a v2

        unify' v@(TCTVarType _ a) t = do
            if not $ occurs a t then
                Right . Subst $ M.singleton a t
            else
                Left $ occursError a t

        unify' t v@(TCTVarType _ a) = do
            if not $ occurs a t then
                Right . Subst $ M.singleton a t
            else
                Left $ occursError a t

        unify' (TCTListType _ a) (TCTListType _ b) = unify' a b

        unify' (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = do
            subst1 <- unify' a1 a2
            subst2 <- unify' (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1

        unify' (TCTFunType _ _ a1 b1) (TCTFunType _ _ a2 b2) = do
            subst1 <- unify a1 a2
            subst2 <- unify (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1

        unify' t1 t2 = Left $ typeMismatchError t1 t2
