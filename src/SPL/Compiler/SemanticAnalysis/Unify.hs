{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SPL.Compiler.SemanticAnalysis.Unify (
    Types(..),
    addSubst,
    generalise,
    occurs,
    occursError,
    liftToScheme,
    typeMismatchError,
    minimizeSubst,
    unify,
    unify'
    ) where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Data.Set.Ordered (OSet)
import Data.Bifunctor (second, Bifunctor (first))
import Control.Monad
import Control.Lens ((^?), ix, (%~), (<>~), (^.), (.~), use)
import Control.Monad.State
import System.Random
import Data.Function ((&))
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Set.Ordered as SO

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error
import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.CoreEntityLocation
import Data.Foldable (fold)
import Data.Graph
import Data.Maybe (fromMaybe)

class Types a where
    ($*) :: Subst -> a -> a
    freeVars :: a -> Set TypeVar

infixr 1 $*

addSubst :: TypeVar -> CoreType -> TCMonad ()
addSubst tv t = modify $
    \st -> let newSubst = Subst . M.insert tv t . unSubst $ st ^. getSubst
            in st & getSubst .~ newSubst
                  & getEnv %~ (newSubst $*)

instance Semigroup Subst where
    -- Subst stores the substitutions in a lazy manner
    -- (i.e. need to traverse the substitutions to get the final type)
    -- Example subst: s = [ b |-> a, a |-> Int ]
    -- then s $* b == Int,
    -- so first b == a, a == Int
    (Subst s1') <> (Subst s2') = Subst (s1' `M.union` s2')

instance Monoid Subst where
    mempty = Subst mempty
    mappend = (<>)

minimizeSubst :: Subst -> Subst
minimizeSubst s@(Subst s') = Subst $ (s $*) <$> s'

instance Types CoreType where
    s $* (CoreIntType l) = CoreIntType l
    s $* (CoreCharType l) = CoreCharType l
    s $* (CoreBoolType l) = CoreBoolType l
    s $* (CoreVoidType l) = CoreVoidType l
    s@(Subst s') $* v@(CoreVarType l a) =
        if M.member a s' then s $* setLoc l (M.findWithDefault v a s') else v
    s $* (CoreListType l a) = CoreListType l (s $* a)
    s $* (CoreTupleType l a b) = CoreTupleType l (s $* a) (s $* b)
    s $* (CoreFunType l a b) = CoreFunType l (s $* a) (s $* b)
    freeVars v@(CoreVarType _ a) = S.singleton a
    freeVars (CoreListType _ a) = freeVars a
    freeVars (CoreTupleType _ a b) = freeVars a <> freeVars b
    freeVars (CoreFunType _ a b) = freeVars a <> freeVars b
    freeVars _ = mempty

instance Types a => Types (Maybe a) where
    s $* Nothing = Nothing
    s $* (Just a) = Just (s $* a)
    freeVars = maybe mempty freeVars

instance Types a => Types [a] where
    s $* xs = map (s $*) xs
    freeVars xs = foldMap freeVars xs

instance (Types a, Ord a) => Types (Set a) where
    s $* xs = S.map (s $*) xs
    freeVars xs = foldMap freeVars xs

instance Types Scheme where
    (Subst s) $* (Scheme tv t) =
        let s' = Subst (foldr M.delete s tv) in Scheme tv (s' $* t)
    freeVars (Scheme tv t) = freeVars t `S.difference` tv

instance Types TypeEnv where
    s $* (TypeEnv env) = TypeEnv $ second (s $*) <$> env
    freeVars (TypeEnv env) = freeVars . map snd $ M.elems env

instance Types Core where
    s $* (Core varDecls funDecls) = Core (map (s $*) varDecls) (map (fmap (s $*)) funDecls)
    freeVars (Core varDecls funDecls) = freeVars varDecls <> foldMap (freeVars . unSCC) funDecls
        where
            unSCC (AcyclicSCC x) = [x]
            unSCC (CyclicSCC xs) = xs

instance Types CoreVarDecl where
    s $* (CoreVarDecl loc t id expr) = CoreVarDecl loc (s $* t) id (s $* expr)
    freeVars (CoreVarDecl _ t _ _) = freeVars t

instance Types CoreFunDecl where
    s $* (CoreFunDecl loc id args t body) =
        CoreFunDecl loc id args (s $* t) (s $* body)
    freeVars (CoreFunDecl _ _ _ t _) = freeVars t

instance Types CoreFunBody where
    s $* (CoreFunBody loc varDecls stmts) = CoreFunBody loc (map (s $*) varDecls) (map (s $*) stmts)
    freeVars (CoreFunBody _ varDecl stmts) = freeVars varDecl <> freeVars stmts

instance Types CoreStmt where
    s $* (IfElseStmt loc e s1 s2) = IfElseStmt loc (s $* e) (s $* s1) (s $* s2)
    s $* (WhileStmt loc e stmt) = WhileStmt loc (s $* e) (s $* stmt)
    s $* (AssignStmt loc i t fd e) = AssignStmt loc i (s $* t) fd (s $* e)
    s $* (ReturnStmt loc me) = ReturnStmt loc (($*) s <$> me)
    s $* (FunCallStmt f) = FunCallStmt (s $* f)
    freeVars (IfElseStmt _ e s1 s2) = freeVars e <> freeVars s1 <> freeVars s2
    freeVars (WhileStmt _ e stmt) = freeVars e <> freeVars stmt
    freeVars (AssignStmt loc i t fd stmt) = freeVars t <> freeVars stmt
    freeVars (ReturnStmt loc me) = maybe mempty freeVars me
    freeVars (FunCallStmt f) = freeVars f

instance Types CoreExpr where
    s $* (FunCallExpr f) = FunCallExpr (s $* f)
    s $* (FunIdentifierExpr t i) = FunIdentifierExpr (s $* t) i
    s $* (OpExpr l op e) = OpExpr l op (s $* e)
    s $* (Op2Expr l e1 t1 op e2 t2) = Op2Expr l (s $* e1) (s $* t1) op (s $* e2) (s $* t2)
    s $* (TupExpr l e1 e2) = TupExpr l (s $* e1) (s $* e2)
    s $* (EmptyListExpr l t) = EmptyListExpr l (s $* t)
    s $* e = e
    freeVars (FunCallExpr f) = freeVars f
    freeVars (OpExpr l op e) = freeVars e
    freeVars (Op2Expr l e1 t1 op e2 t2) = freeVars e1 <> freeVars t1 <> freeVars e2 <> freeVars t2
    freeVars (TupExpr l e1 e2) = freeVars e1 <> freeVars e2
    freeVars (EmptyListExpr l t) = freeVars t
    freeVars _ = mempty

instance Types CoreFunCall where
    s $* (CoreFunCall l e t args) = CoreFunCall l (s $* e) (s $* t) (s $* args)
    freeVars (CoreFunCall _ _ t args) = freeVars t <> freeVars args

generalise :: CoreType -> TCMonad Scheme
generalise t = do
    subst <- use getSubst
    env <- use getEnv
    let t' = subst $* t
        freeTV = freeVars t' `S.difference` freeVars env
    pure $ Scheme freeTV t'

-- liftToScheme lifts a type to a scheme that has no quantified variables
liftToScheme :: CoreType -> Scheme
liftToScheme = Scheme mempty

typeMismatchError :: (MonadTrans t, MonadState s (t (Either Error)), ContainsSource s) =>
                     CoreType -> CoreType -> t (Either Error) a
typeMismatchError expT actT = do
    let header = [ T.pack $
            "Couldn't match expected type '" <> show expT <>
            "' with actual type '" <> show actT <> "'."
            ]
    typeLocTrace <- definition (T.pack $ "'" <>
                                         show expT <>
                                         "' has been inferred as the type of: ")
                                actT
    throwErr $ header <> typeLocTrace


occurs :: TypeVar -> CoreType -> Bool
occurs var t = S.member var (freeVars t)

occursError :: (MonadTrans t, MonadState s (t (Either Error)), ContainsSource s) =>
                TypeVar -> CoreType -> t (Either Error) a
occursError var t = do
    typeLocTrace <- definition (T.pack $ "'" <>
                                         show t <>
                                         "' has been inferred as the type of: "
                               ) t
    throwErr $ [
        "Occurs check: cannot construct the infinite type: "
        <> var
        <> " ~ "
        <> T.pack (show t)
        ] <> typeLocTrace

unify :: CoreType -> CoreType -> TCMonad ()
unify expT actT = do
    s <- use getSubst
    Subst subst <- unify' (s $* expT) (s $* actT)
    mapM_ (uncurry addSubst) $ M.toList subst

unify' :: (MonadTrans t, MonadState s (t (Either Error)), ContainsSource s) =>
          CoreType -> CoreType -> t (Either Error) Subst
unify' CoreIntType{} CoreIntType{} = return mempty
unify' CoreCharType{} CoreCharType{} = return mempty
unify' CoreBoolType{} CoreBoolType{} = return mempty
unify' CoreVoidType{} CoreVoidType{} = return mempty

unify' v1@(CoreVarType _ a) v2@(CoreVarType _ b)
    | a == b = return mempty
    | otherwise = pure . Subst $ M.singleton a v2

unify' v@(CoreVarType _ a) t = do
    if not $ occurs a t then
        pure . Subst $ M.singleton a t
    else
        occursError a t

unify' t v@(CoreVarType _ a) = do
    if not $ occurs a t then
        pure . Subst $ M.singleton a t
    else
        occursError a t

unify' (CoreListType _ a) (CoreListType _ b) = unify' a b

unify' (CoreTupleType _ a1 b1) (CoreTupleType _ a2 b2) = do
    subst <- unify' a1 a2
    (subst <>) <$> unify' (subst $* b1) (subst $* b2)

unify' (CoreFunType _ Nothing r1) (CoreFunType _ Nothing r2) = do
    unify' r1 r2

unify' t1@(CoreFunType _ (Just a1) r1) t2@(CoreFunType _ (Just a2) r2) = do
    subst <- unify' a1 a2
    (subst <>) <$> unify' (subst $* r1) (subst $* r2)

unify' t1 t2 = typeMismatchError t1 t2
