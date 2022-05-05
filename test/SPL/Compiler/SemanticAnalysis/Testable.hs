{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module SPL.Compiler.SemanticAnalysis.Testable where

import Data.Default
import Data.Text (Text)
import qualified Data.Text as T
import GHC.TypeLits
import Data.Proxy
import qualified Data.Set as S

import SPL.Compiler.Common.Testable
import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TreeTransformer
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import SPL.Compiler.SemanticAnalysis.TCTEntityLocation

instance Testable TCTIdentifier where
    toTestForm (TCTIdentifier _ i) = TCTIdentifier def i

instance Testable TCTFunCall where
    toTestForm (TCTFunCall _ i t e) = TCTFunCall def (toTestForm i) (toTestForm t) (toTestForm e)

instance Testable TCTType where
    toTestForm (TCTFunType _ c t1 t2) = TCTFunType def c (toTestForm t1) (toTestForm t2)
    toTestForm (TCTTupleType _ c t1 t2) = TCTTupleType def c (toTestForm t1) (toTestForm t2)
    toTestForm (TCTListType _ c t) = TCTListType def c (toTestForm t)
    toTestForm (TCTVarType _ c v) = TCTVarType def c v
    toTestForm (TCTIntType _ c) = TCTIntType def c
    toTestForm (TCTBoolType _ c) = TCTBoolType def c
    toTestForm (TCTCharType _ c) = TCTCharType def c
    toTestForm (TCTVoidType _ c) = TCTVoidType def c

instance Testable TCTField where
    toTestForm (Hd _) = Hd def
    toTestForm (Tl _) = Tl def
    toTestForm (Fst _) = Fst def
    toTestForm (Snd _) = Snd def

instance Testable TCTFieldSelector where
    toTestForm (TCTFieldSelector _ i t fs) = TCTFieldSelector def (toTestForm i) (toTestForm t) (toTestForm fs)

instance Testable TCTExpr where
    toTestForm (TupExpr _ p1 p2) = TupExpr def (toTestForm p1) (toTestForm p2)
    toTestForm (FunCallExpr c) = FunCallExpr (toTestForm c)
    toTestForm (FieldSelectExpr i) = FieldSelectExpr (toTestForm i)
    toTestForm (IntExpr _ i) = IntExpr def i
    toTestForm (CharExpr _ c) = CharExpr def c
    toTestForm (BoolExpr _ b) = BoolExpr def b
    toTestForm (OpExpr _ o e) = OpExpr def o (toTestForm e)
    toTestForm (Op2Expr _ e1 o e2) = Op2Expr def (toTestForm e1) o (toTestForm e2)
    toTestForm (EmptyListExpr _ t) = EmptyListExpr def (toTestForm t)

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
    expr [] = EmptyListExpr def (unknownType def)
    expr (x:xs) = Op2Expr def (expr x) Cons (expr xs)

instance (ToExpr a, ToExpr b) => ToExpr (a,b) where
    expr (a,b) = TupExpr def (expr a) (expr b)

instance ToExpr TCTFunCall where
    expr f = FunCallExpr f

instance ToExpr TCTFieldSelector where
    expr f = FieldSelectExpr f

fun1 :: ToExpr a => Text -> a -> TCTFunCall
fun1 id e = TCTFunCall def (TCTIdentifier def id) (unknownType def) [expr e]

fun2 :: (ToExpr a, ToExpr b) => Text -> a -> b -> TCTFunCall
fun2 id e1 e2 = TCTFunCall def (TCTIdentifier def id) (unknownType def) [expr e1, expr e2]

fun3 :: (ToExpr a, ToExpr b, ToExpr c) => Text -> a -> b -> c -> TCTFunCall
fun3 id e1 e2 e3 = TCTFunCall def (TCTIdentifier def id) (unknownType def) [expr e1, expr e2, expr e3]

op1 :: (ToExpr a) => OpUnary -> a -> TCTExpr
op1 op e = OpExpr def op (expr e)

op2 :: (ToExpr a, ToExpr b) => a -> OpBin -> b -> TCTExpr
op2 e1 op e2 = Op2Expr def (expr e1) op (expr e2)

ident = TCTIdentifier def

iexpr = expr @Int

emptyList :: TCTExpr
emptyList = EmptyListExpr def (unknownType def)

fd :: Text -> [TCTField] -> TCTFieldSelector
fd name = TCTFieldSelector def (ident name) (unknownType def) 

class ToType a where
    toType :: Proxy a -> TCTType

instance ToType Int where
    toType _ = TCTIntType def mempty

instance ToType Bool where
    toType _ = TCTBoolType def mempty

instance ToType Char where
    toType _ = TCTCharType def mempty

instance KnownSymbol a => ToType (TVar (a :: Symbol)) where
    toType p = TCTVarType def mempty (T.pack . symbolVal $ Proxy @a)

instance ToType a => ToType [a] where
    toType _ = TCTListType def mempty (toType (Proxy @a))

instance (ToType a, ToType b) => ToType (a,b) where
    toType _ = TCTTupleType def mempty (toType (Proxy @a)) (toType (Proxy @b))

instance (ToType a, ToType b) => ToType ((->) a b) where
    toType _ = TCTFunType def mempty (toType (Proxy @a)) (toType (Proxy @b))

data TVar a = TVar

typ :: forall a. ToType a => TCTType
typ = toType (Proxy :: Proxy a)


class ToStmt a where
    stmt :: a -> TCTStmt

instance ToStmt TCTStmt where
    stmt = id

instance ToStmt TCTFunCall where
    stmt = FunCallStmt def

ite :: ToExpr a => a -> [TCTStmt] -> [TCTStmt] -> TCTStmt
ite c = IfElseStmt def (expr c)

while :: ToExpr a => a -> [TCTStmt] -> TCTStmt
while c = WhileStmt def (expr c)

infixl 2 =:

(=:) :: ToExpr a => TCTFieldSelector -> a -> TCTStmt
(=:) fd x = AssignStmt def fd (expr x)

ret :: ToExpr a => a -> TCTStmt
ret a = ReturnStmt def (Just . expr $ a)

retVoid :: TCTStmt
retVoid = ReturnStmt def Nothing

defineI :: Text -> TCTExpr -> TCTVarDecl
defineI id  = TCTVarDecl def (TCTVarType def mempty "") (TCTIdentifier def id)

define :: Text -> TCTType -> TCTExpr -> TCTVarDecl
define id t = TCTVarDecl def t (TCTIdentifier def id)

declare :: Text -> [Text] -> TCTType -> [TCTVarDecl] -> [TCTStmt] -> TCTFunDecl
declare id args tau vs stmt =
    TCTFunDecl def
               (TCTIdentifier def id)
               (map (TCTIdentifier def) args)
               tau
               (TCTFunBody def vs stmt)
