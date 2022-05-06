{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SPL.Compiler.SemanticAnalysis.TypeCheck.Unify where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Data.Bifunctor (second)
import Control.Monad
import Control.Lens ((^?), ix)
import Control.Monad.State
import System.Random
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error
import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TypeCheck.TCon
import SPL.Compiler.SemanticAnalysis.TCTEntityLocation

class Types a where
    ($*) :: Subst -> a -> a
    freeVars :: a -> Set TypeVar

infixr 1 $*

instance Semigroup Subst where
    -- `(s1 <> s2) t` means 
    -- first apply `s2` to `t` and then apply `s1` on result
    -- Note that composition of substitutions is not commutative 
    s1@(Subst s1') <> (Subst s2') = Subst ( (($*) s1 <$> s2') `M.union` s1')

instance Monoid Subst where
    mempty = Subst mempty
    mappend = (<>)

instance Types TCTType where
    s $* (TCTIntType e c) = TCTIntType e (s $* c)
    s $* (TCTCharType e c) = TCTCharType e (s $* c)
    s $* (TCTBoolType e c) = TCTBoolType e (s $* c)
    s $* (TCTVoidType e c) = TCTVoidType e (s $* c)
    s@(Subst s') $* v@(TCTVarType l c a) = updateTCon (s $* c) $ setLoc l (M.findWithDefault v a s')
    s $* (TCTListType e c a) = TCTListType e (s $* c) (s $* a)
    s $* (TCTTupleType e c a b) = TCTTupleType e (s $* c) (s $* a) (s $* b)
    s $* (TCTFunType d e a b) = TCTFunType d (s $* e) (s $* a) (s $* b)
    freeVars v@(TCTVarType l _ a) = S.singleton a
    freeVars (TCTListType _ _ a) = freeVars a
    freeVars (TCTTupleType _ _ a b) = freeVars a <> freeVars b
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
    s $* (TypeEnv env) = TypeEnv $ second (s $*) <$> env
    freeVars (TypeEnv env) = freeVars . map snd $ M.elems env

instance Types TCT where
    s $* (TCT varDecls funDecls) = TCT (map (s $*) varDecls) (map (map (s $*)) funDecls)
    freeVars (TCT varDecls funDecls) = freeVars varDecls <> foldMap (foldMap freeVars) funDecls

instance Types TCTVarDecl where
    s $* (TCTVarDecl loc t id expr) = TCTVarDecl loc (s $* t) id expr
    freeVars (TCTVarDecl _ t _ _) = freeVars t

instance Types TCTFunDecl where
    s $* (TCTFunDecl loc id args t body) = TCTFunDecl loc id args (s $* t) (s $* body)
    freeVars (TCTFunDecl loc id args t body) = freeVars t

instance Types TCTFunBody where
    s $* (TCTFunBody loc varDecls stmts) = TCTFunBody loc (map (s $*) varDecls) (map (s $*) stmts)
    freeVars (TCTFunBody _ varDecl stmts) = freeVars varDecl

instance Types TCTStmt where
    s $* (IfElseStmt loc e s1 s2) = IfElseStmt loc (s $* e) (s $* s1) (s $* s2)
    s $* (WhileStmt loc e stmt) = WhileStmt loc (s $* e) (s $* stmt)
    s $* (AssignStmt loc fd stmt) = AssignStmt loc fd (s $* stmt)
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
    freeVars e = mempty

instance Types TCTFunCall where
    s $* (TCTFunCall l id t args) = TCTFunCall l id (s $* t) (s $* args)
    freeVars (TCTFunCall _ _ t args) = freeVars t <> freeVars args

instance Types TCTFieldSelector where
    s $* (TCTFieldSelector l id t fds) = TCTFieldSelector l id (s $* t) fds
    freeVars (TCTFieldSelector _ _ t _) = freeVars t

generalise :: TypeEnv -> TCTType -> Scheme
generalise env t = Scheme (freeVars t `S.difference` freeVars env) t

-- liftToScheme lifts a type to a scheme that has no quantified variables
liftToScheme :: TCTType -> Scheme
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

unify :: TCTType -> TCTType -> TCMonad Subst
unify t1 t2 = unify' t1 t2
    where
        unify' :: TCTType -> TCTType -> TCMonad Subst
        unify' TCTIntType{} TCTIntType{} = return mempty
        unify' TCTCharType{} TCTCharType{} = return mempty
        unify' TCTBoolType{} TCTBoolType{} = return mempty
        unify' TCTVoidType{} TCTVoidType{} = return mempty

        unify' v1@(TCTVarType _ _ a) v2@(TCTVarType _ _ b)
            | a == b = return mempty
            | otherwise = return . Subst $ M.singleton a v2

        unify' v@(TCTVarType _ _ a) t = do
            if not $ occurs a t then
                return . Subst $ M.singleton a t
            else
                occursError a t

        unify' t v@(TCTVarType _ _ a) = do
            if not $ occurs a t then
                return . Subst $ M.singleton a t
            else
                occursError a t

        unify' (TCTListType _ _ a) (TCTListType _ _ b) = unify' a b

        unify' (TCTTupleType _ _ a1 b1) (TCTTupleType _ _ a2 b2) = do
            subst1 <- unify' a1 a2
            subst2 <- unify' (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1

        unify' (TCTFunType _ _ a1 b1) (TCTFunType _ _ a2 b2) = do
            subst1 <- unify a1 a2
            subst2 <- unify (subst1 $* b1) (subst1 $* b2)
            return $ subst2 <> subst1

        unify' t1 t2 = typeMismatchError t1 t2
