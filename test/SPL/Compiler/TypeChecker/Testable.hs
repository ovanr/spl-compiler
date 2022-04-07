{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module SPL.Compiler.TypeChecker.Testable where

import Data.Default
import Data.Text (Text)
import qualified Data.Text as T
import GHC.TypeLits
import Data.Proxy
import qualified Data.Set as S

import SPL.Compiler.Common.Testable
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.Unify
import SPL.Compiler.TypeChecker.TCTEntityLocation

instance Testable TCTIdentifier where
    toTestForm (TCTIdentifier _ i) = TCTIdentifier def i

instance Testable TCTFunCall where
    toTestForm (TCTFunCall _ i e) = TCTFunCall def (toTestForm i) (toTestForm e)

instance Testable TCTType where
    toTestForm (TCTFunType _ d t1 t2) = TCTFunType def d (toTestForm t1) (toTestForm t2)
    toTestForm (TCTTupleType _ t1 t2) = TCTTupleType def (toTestForm t1) (toTestForm t2)
    toTestForm (TCTListType _ t) = TCTListType def (toTestForm t)
    toTestForm (TCTVarType _ v) = TCTVarType def v
    toTestForm (TCTIntType _) = TCTIntType def
    toTestForm (TCTBoolType _) = TCTBoolType def
    toTestForm (TCTCharType _) = TCTCharType def
    toTestForm (TCTVoidType _) = TCTVoidType def

instance Testable TCTField where
    toTestForm (Hd _) = Hd def
    toTestForm (Tl _) = Tl def
    toTestForm (Fst _) = Fst def
    toTestForm (Snd _) = Snd def

instance Testable TCTFieldSelector where
    toTestForm (TCTFieldSelector _ i fs) = TCTFieldSelector def (toTestForm i) (toTestForm fs)

instance Testable TCTExpr where
    toTestForm (TupExpr _ p1 p2) = TupExpr def (toTestForm p1) (toTestForm p2)
    toTestForm (FunCallExpr c) = FunCallExpr (toTestForm c)
    toTestForm (FieldSelectExpr i) = FieldSelectExpr (toTestForm i)
    toTestForm (IntExpr _ i) = IntExpr def i
    toTestForm (CharExpr _ c) = CharExpr def c
    toTestForm (BoolExpr _ b) = BoolExpr def b
    toTestForm (OpExpr _ o e) = OpExpr def o (toTestForm e)
    toTestForm (Op2Expr _ e1 o e2) = Op2Expr def (toTestForm e1) o (toTestForm e2)
    toTestForm (EmptyListExpr _ ) = EmptyListExpr def

instance Testable TCTVarDecl where
    toTestForm (TCTVarDecl _ t i e) = TCTVarDecl def (toTestForm t) (toTestForm i) (toTestForm e)

instance Testable TCTFunDecl where
    toTestForm (TCTFunDecl _ i is t b) =
        TCTFunDecl def (toTestForm i) (toTestForm is) (toTestForm t) (toTestForm b)

instance Testable TCTFunBody where
    toTestForm (TCTFunBody _ v s) = TCTFunBody def (toTestForm v) (toTestForm s)

instance Testable TCTStmt where
    toTestForm (IfElseStmt _ val1 val2 val3) = IfElseStmt def (toTestForm val1) (toTestForm val2) (toTestForm val3)
    toTestForm (WhileStmt _ val1 val2) = WhileStmt def (toTestForm val1) (toTestForm val2)
    toTestForm (AssignStmt _ val1 val2) = AssignStmt def (toTestForm val1) (toTestForm val2)
    toTestForm (FunCallStmt _ val1) = FunCallStmt def (toTestForm val1)
    toTestForm (ReturnStmt _ val1) = ReturnStmt def (toTestForm val1)

instance Testable Subst where
    toTestForm (Subst var) = Subst $ toTestForm <$> var

class ToExpr a where
    expr :: a -> TCTExpr

data Nop

instance ToExpr Nop where
    expr = undefined

instance ToExpr Int where
    expr i = IntExpr def (fromIntegral i)

instance ToExpr Bool where
    expr b = BoolExpr def b

instance ToExpr Char where
    expr c = CharExpr def c

instance ToExpr TCTExpr where
    expr e = e

instance ToExpr a => ToExpr [a] where
    expr [] = EmptyListExpr def
    expr (x:xs) = Op2Expr def (expr x) Cons (expr xs)

instance (ToExpr a, ToExpr b) => ToExpr (a,b) where
    expr (a,b) = TupExpr def (expr a) (expr b)

instance ToExpr TCTFunCall where
    expr f = FunCallExpr f

instance ToExpr TCTFieldSelector where
    expr f = FieldSelectExpr f

fun1 :: ToExpr a => Text -> a -> TCTFunCall
fun1 id e = TCTFunCall def (TCTIdentifier def id) [expr e]

fun2 :: (ToExpr a, ToExpr b) => Text -> a -> b -> TCTFunCall
fun2 id e1 e2 = TCTFunCall def (TCTIdentifier def id) [expr e1, expr e2]

fun3 :: (ToExpr a, ToExpr b, ToExpr c) => Text -> a -> b -> c -> TCTFunCall
fun3 id e1 e2 e3 = TCTFunCall def (TCTIdentifier def id) [expr e1, expr e2, expr e3]

op1 :: (ToExpr a) => OpUnary -> a -> TCTExpr
op1 op e = OpExpr def op (expr e)

op2 :: (ToExpr a, ToExpr b) => a -> OpBin -> b -> TCTExpr
op2 e1 op e2 = Op2Expr def (expr e1) op (expr e2)

ident = TCTIdentifier def

iexpr = expr @Int

emptyList :: TCTExpr
emptyList = EmptyListExpr def

fd :: Text -> [TCTField] -> TCTFieldSelector
fd name = TCTFieldSelector def (ident name)

class ToType a where
    toType :: Proxy a -> TCTType

instance ToType Int where
    toType _ = TCTIntType def

instance ToType Bool where
    toType _ = TCTBoolType def

instance ToType Char where
    toType _ = TCTCharType def

instance KnownSymbol a => ToType (Var (a :: Symbol)) where
    toType p = TCTVarType def (T.pack . symbolVal $ Proxy @a)

instance ToType a => ToType [a] where
    toType _ = TCTListType def (toType (Proxy @a))

instance (ToType a, ToType b) => ToType (a,b) where
    toType _ = TCTTupleType def (toType (Proxy @a)) (toType (Proxy @b))

instance (ToType a, ToType b) => ToType ((->) a b) where
    toType _ = TCTFunType def [] (toType (Proxy @a)) (toType (Proxy @b))

data Var a = Var

typ :: forall a. ToType a => TCTType
typ = toType (Proxy :: Proxy a)

