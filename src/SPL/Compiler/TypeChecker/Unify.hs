{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SPL.Compiler.TypeChecker.Unify where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad
import Control.Lens ((^?), ix)
import Control.Monad.State
import System.Random
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.TCon
import SPL.Compiler.TypeChecker.TCTEntityLocation
import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error

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
    s $* (TCTFunType d e a b) = TCTFunType d (s $* e) (s $* a) (s $* b)
    freeVars v@(TCTVarType l a) = S.singleton a
    freeVars (TCTListType _ a) = freeVars a
    freeVars (TCTTupleType _ a b) = freeVars a <> freeVars b
    freeVars (TCTFunType _ _ a b) = freeVars a <> freeVars b
    freeVars _ = mempty

instance Types TCon where
    s $* (TEq t) = TEq (s $* t)
    s $* (TOrd t) = TOrd (s $* t)
    s $* (TPrint t) = TPrint (s $* t)
    freeVars (TEq t) = freeVars t
    freeVars (TOrd t) = freeVars t
    freeVars (TPrint t) = freeVars t

instance Types a => Types [a] where
    s $* xs = map (s $*) xs
    freeVars xs = foldMap freeVars xs

instance (Types a, Ord a) => Types (Set a) where
    s $* xs = S.map (s $*) xs
    freeVars xs = foldMap freeVars xs

instance Types Scheme where
    (Subst s) $* (Scheme tv t) = Scheme tv $ Subst (foldr M.delete s tv) $* t
    freeVars (Scheme tv t) = freeVars t `S.difference` tv

instance Types TypeEnv where
    s $* (TypeEnv env) = TypeEnv $ ($*) s <$> env
    freeVars (TypeEnv env) = freeVars $ M.elems env

instance Types TCT where
    s $* (TCT leaves) = TCT $ map (s $*) leaves
    freeVars (TCT leaves) = freeVars leaves

instance Types TCTLeaf where
    s $* (TCTVar varDecl) = TCTVar $ s $* varDecl
    s $* (TCTFun funDecl) = TCTFun $ s $* funDecl
    freeVars (TCTVar varDecl) = freeVars varDecl
    freeVars (TCTFun funDecl) = freeVars funDecl

instance Types TCTVarDecl where
    s $* (TCTVarDecl loc t id expr) = TCTVarDecl loc (s $* t) id expr
    freeVars (TCTVarDecl _ t _ _) = freeVars t

instance Types TCTFunDecl where
    s $* (TCTFunDecl loc id args t body) = TCTFunDecl loc id args (s $* t) (s $* body)
    freeVars (TCTFunDecl loc id args t body) = freeVars t

instance Types TCTFunBody where
    s $* (TCTFunBody loc varDecls stmts) = TCTFunBody loc (map (s $*) varDecls) stmts
    freeVars (TCTFunBody _ varDecl stmts) = freeVars varDecl

generalise :: TypeEnv -> TCTType -> Scheme
generalise env t = Scheme (freeVars t `S.difference` freeVars env) t

liftToScheme :: TCTType -> Scheme
liftToScheme = Scheme mempty

typeMismatchError :: TCTType -> TCTType -> TCMonad a
typeMismatchError expT actT = do
    let header = [ T.pack $
            "Couldn't match expected type '" <> show expT <> 
            "' with actual type '" <> show actT <> "'"
            ]
    typeLocTrace <- definition (T.pack $ "'" <> 
                                         show expT <> 
                                         "' has been inferred as the type of: ") 
                                actT
    tcError $ header <> typeLocTrace


occurs :: TypeVar -> TCTType -> Bool
occurs var t = S.member var (freeVars t)

occursError :: TypeVar -> TCTType -> TCMonad a
occursError var t = do
    typeLocTrace <- definition (T.pack $ "'" <> 
                                         show t <> 
                                         "' has been inferred as the type of: "
                               ) t
    tcError $ [
        "Occurs check: cannot construct the infinite type: "
        <> var
        <> " ~ "
        <> T.pack (show t)
        ] <> typeLocTrace

unify :: TCTType -> TCTType -> TCMonad Subst
unify t1 t2 = unify' t1 t2
    where
        unify' :: TCTType -> TCTType -> TCMonad Subst
        unify' (TCTIntType _) (TCTIntType _) = return mempty
        unify' (TCTCharType _) (TCTCharType _) = return mempty
        unify' (TCTBoolType _) (TCTBoolType _) = return mempty
        unify' (TCTVoidType _) (TCTVoidType _) = return mempty

        unify' v1@(TCTVarType _ a) v2@(TCTVarType _ b)
            | a == b = return mempty
            | otherwise = return . Subst $ M.singleton a v2

        unify' v@(TCTVarType _ a) t = do
            if not $ occurs a t then
                return . Subst $ M.singleton a t
            else
                occursError a t

        unify' t v@(TCTVarType _ a) = do
            if not $ occurs a t then
                return . Subst $ M.singleton a t
            else
                occursError a t

        unify' (TCTListType _ a) (TCTListType _ b) = unify' a b

        unify' (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = do
            subst1 <- unify' a1 a2
            subst2 <- unify' (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1

        unify' (TCTFunType _ _ a1 b1) (TCTFunType _ _ a2 b2) = do
            subst1 <- unify a1 a2
            subst2 <- unify (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1

        unify' t1 t2 = typeMismatchError t1 t2
