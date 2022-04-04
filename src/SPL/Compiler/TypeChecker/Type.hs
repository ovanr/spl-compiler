{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.TypeChecker.Type where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

type Error = Text

newtype Subst = Subst (Map TypeVar Type) deriving (Eq, Show)

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

substApply :: Subst -> Type -> Type
substApply _ IntType = IntType
substApply _ CharType = CharType
substApply _ BoolType = BoolType
substApply _ VoidType = VoidType
substApply (Subst s) v@(VarType a) = M.findWithDefault v a s
substApply s (ListType a) = ListType (substApply s a)
substApply s (TupleType a b) = TupleType (substApply s a) (substApply s b)
substApply s (FunType a b) = FunType (substApply s a) (substApply s b)

typeVars :: Type -> Set TypeVar
typeVars (VarType a) = S.singleton a
typeVars (FunType a b) = typeVars a <> typeVars b
typeVars (TupleType a b) = typeVars a <> typeVars b
typeVars (ListType a) = typeVars a
typeVars _ = S.empty

occurs :: TypeVar -> Type -> Bool
occurs var t = S.member var (typeVars t)
occursError :: TypeVar -> Type -> Error
occursError var t =
    "Occurs check: cannot construct the infinite type: "
        <> var 
        <> " ~ " 
        <> T.pack (show t)

unify :: Type -> Type -> Either Error Subst
unify IntType IntType = Right mempty
unify CharType CharType = Right mempty
unify BoolType BoolType = Right mempty
unify VoidType VoidType = Right mempty
unify (VarType a) v2@(VarType b)
    | a == b = Right mempty
    | otherwise = Right . Subst $ M.singleton a v2
unify (VarType a) t =
    if not $ occurs a t then
        Right . Subst $ M.singleton a t
    else
        Left $ occursError a t
unify t (VarType a) =
    if not $ occurs a t then
        Right . Subst $ M.singleton a t
    else
        Left $ occursError a t
unify (ListType a) (ListType b) = unify a b
unify (TupleType a1 b1) (TupleType a2 b2) = do
    subst1 <- unify a1 a2 
    subst2 <- unify (substApply subst1 b1) (substApply subst1 b2)
    return $ subst2 <> subst1
unify (FunType a1 b1) (FunType a2 b2) = do
    subst1 <- unify a1 a2 
    subst2 <- unify (substApply subst1 b1) (substApply subst1 b2)
    return $ subst2 <> subst1
unify t1 t2 = Left $ 
    "Couldn't match type '" <> T.pack (show t1) 
                            <> "' with '" 
                            <> T.pack (show t2)
                            <> "'"
