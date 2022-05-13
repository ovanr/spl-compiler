{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SPL.Compiler.SemanticAnalysis.TypeCheck.Unify (
    Types(..),
    addSubst,
    generalise,
    occurs,
    occursError,
    liftToScheme,
    typeMismatchError,
    minimizeSubst,
    unify
    ) where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Data.Bifunctor (second)
import Control.Monad
import Control.Lens ((^?), ix, (%~), (<>~), (^.), (.~), use)
import Control.Monad.State
import System.Random
import Data.Function ((&))
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error
import SPL.Compiler.SemanticAnalysis.TCT
import {-# SOURCE #-} SPL.Compiler.SemanticAnalysis.TypeCheck.TCon
import SPL.Compiler.SemanticAnalysis.TCTEntityLocation

class Types a where
    ($*) :: Subst -> a -> a
    freeVars :: a -> Set TypeVar

infixr 1 $*

addSubst :: TypeVar -> TCTType -> TCMonad ()
addSubst tv t = modify $
    \st -> let newSubst = Subst . M.insert tv t . unSubst $ st ^. getSubst
            in st & getSubst .~ newSubst
                  & getEnv %~ (newSubst $*)
                  & getTcons %~ (L.nub . (newSubst $*))

instance Semigroup Subst where
    -- Subst stores the substitutions in a lazy manner
    -- (i.e. need to traverse the substitutions to get the final type)
    -- Example subst: s = [ b |-> a, a |-> Int ]
    -- then s $* b == Int,
    -- so first b == a, a == Int
    -- 
    (Subst s1') <> (Subst s2') = Subst (s1' `M.union` s2')

instance Monoid Subst where
    mempty = Subst mempty
    mappend = (<>)

minimizeSubst :: Subst -> Subst
minimizeSubst s@(Subst s') = Subst $ (s $*) <$> s'

instance Types TCTType where
    s $* (TCTIntType l) = TCTIntType l
    s $* (TCTCharType l) = TCTCharType l
    s $* (TCTBoolType l) = TCTBoolType l
    s $* (TCTVoidType l) = TCTVoidType l
    s@(Subst s') $* v@(TCTVarType l a) =
        if M.member a s' then s $* setLoc l (M.findWithDefault v a s') else v
    s $* (TCTListType l a) = TCTListType l (s $* a)
    s $* (TCTTupleType l a b) = TCTTupleType l (s $* a) (s $* b)
    s $* (TCTFunType l a b) = TCTFunType l (s $* a) (s $* b)
    freeVars v@(TCTVarType _ a) = S.singleton a
    freeVars (TCTListType _ a) = freeVars a
    freeVars (TCTTupleType _ a b) = freeVars a <> freeVars b
    freeVars (TCTFunType _ a b) = freeVars a <> freeVars b
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
    (Subst s) $* (Scheme tv tcons t) =
        let s' = Subst (foldr M.delete s tv) in Scheme tv (s' $* tcons) (s' $* t)
    freeVars (Scheme tv _ t) = freeVars t `S.difference` tv

instance Types TypeEnv where
    s $* (TypeEnv env) = TypeEnv $ second (s $*) <$> env
    freeVars (TypeEnv env) = freeVars . map snd $ M.elems env

instance Types TCT where
    s $* (TCT varDecls funDecls) = TCT (map (s $*) varDecls) (map (map (s $*)) funDecls)
    freeVars (TCT varDecls funDecls) = freeVars varDecls <> foldMap (foldMap freeVars) funDecls

instance Types TCTVarDecl where
    s $* (TCTVarDecl loc t id expr) = TCTVarDecl loc (s $* t) id expr
    freeVars (TCTVarDecl _ t _ _) = freeVars t

instance Types TCTFunDecl where
    s $* (TCTFunDecl loc id args t tcons body) = TCTFunDecl loc id args (s $* t) (s $* tcons) (s $* body)
    freeVars (TCTFunDecl _ _ _ t _ _) = freeVars t

instance Types TCTFunBody where
    s $* (TCTFunBody loc varDecls stmts) = TCTFunBody loc (map (s $*) varDecls) (map (s $*) stmts)
    freeVars (TCTFunBody _ varDecl stmts) = freeVars varDecl <> freeVars stmts

instance Types TCTStmt where
    s $* (IfElseStmt loc e s1 s2) = IfElseStmt loc (s $* e) (s $* s1) (s $* s2)
    s $* (WhileStmt loc e stmt) = WhileStmt loc (s $* e) (s $* stmt)
    s $* (AssignStmt loc fd stmt) = AssignStmt loc (s $* fd) (s $* stmt)
    s $* (ReturnStmt loc me) = ReturnStmt loc (($*) s <$> me)
    s $* (FunCallStmt l f) = FunCallStmt l (s $* f)
    freeVars (IfElseStmt _ e s1 s2) = freeVars e <> freeVars s1 <> freeVars s2
    freeVars (WhileStmt _ e stmt) = freeVars e <> freeVars stmt
    freeVars (AssignStmt loc fd stmt) = freeVars stmt
    freeVars (ReturnStmt loc me) = maybe mempty freeVars me
    freeVars (FunCallStmt l f) = freeVars f

instance Types TCTExpr where
    s $* (FunCallExpr f) = FunCallExpr (s $* f)
    s $* (FieldSelectExpr fd) = FieldSelectExpr (s $* fd)
    s $* (OpExpr l op e) = OpExpr l op (s $* e)
    s $* (Op2Expr l e1 op e2) = Op2Expr l (s $* e1) op (s $* e2)
    s $* (TupExpr l e1 e2) = TupExpr l (s $* e1) (s $* e2)
    s $* (EmptyListExpr l t) = EmptyListExpr l (s $* t)
    s $* e = e
    freeVars (FunCallExpr f) = freeVars f
    freeVars (FieldSelectExpr fd) = freeVars fd
    freeVars (OpExpr l op e) = freeVars e
    freeVars (Op2Expr l e1 op e2) = freeVars e1 <> freeVars e2
    freeVars (TupExpr l e1 e2) = freeVars e1 <> freeVars e2
    freeVars (EmptyListExpr l t) = freeVars t
    freeVars _ = mempty

instance Types TCTFunCall where
    s $* (TCTFunCall l id t tcons args) = TCTFunCall l id (s $* t) (s $* tcons) (s $* args)
    freeVars (TCTFunCall _ _ t _ args) = freeVars t <> freeVars args

instance Types TCTFieldSelector where
    s $* (TCTFieldSelector l id t fds) = TCTFieldSelector l id (s $* t) fds
    freeVars (TCTFieldSelector _ _ t _) = freeVars t

generalise :: TCTType -> [TCon] -> TCMonad Scheme
generalise t tcon = do
    subst <- use getSubst
    env <- use getEnv
    let t' = subst $* t
    pure $ Scheme (freeVars t' `S.difference` freeVars env) (subst $* tcon) t'

-- liftToScheme lifts a type to a scheme that has no quantified variables
liftToScheme :: [TCon] -> TCTType -> Scheme
liftToScheme = Scheme mempty

typeMismatchError :: TCTType -> TCTType -> TCMonad a
typeMismatchError expT actT = do
    let header = [ T.pack $
            "Couldn't match expected type '" <> show expT <>
            "' with actual type '" <> show actT <> "'."
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

unify :: TCTType -> TCTType -> TCMonad ()
unify expT actT = use getSubst >>= (\s -> unify' (s $* expT) (s $* actT))
    where
        unify' TCTIntType{} TCTIntType{} = return ()
        unify' TCTCharType{} TCTCharType{} = return ()
        unify' TCTBoolType{} TCTBoolType{} = return ()
        unify' TCTVoidType{} TCTVoidType{} = return ()

        unify' v1@(TCTVarType _ a) v2@(TCTVarType _ b)
            | a == b = return ()
            | otherwise = addSubst a v2

        unify' v@(TCTVarType _ a) t = do
            if not $ occurs a t then
                addSubst a t
            else
                occursError a t

        unify' t v@(TCTVarType _ a) = do
            if not $ occurs a t then
                addSubst a t
            else
                occursError a t

        unify' (TCTListType _ a) (TCTListType _ b) = unify' a b

        unify' (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = do
            unify' a1 a2
            subst <- use getSubst
            unify' (subst $* b1) (subst $* b2)

        unify' (TCTFunType _ a1 b1) (TCTFunType _ a2 b2) = do
            unify' a1 a2
            subst <- use getSubst
            unify' (subst $* b1) (subst $* b2)

        unify' t1 t2 = typeMismatchError t1 t2
