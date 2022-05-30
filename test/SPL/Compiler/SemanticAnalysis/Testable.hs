{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module SPL.Compiler.SemanticAnalysis.Testable where

import Data.Default
import Data.Text (Text)
import qualified Data.Text as T
import GHC.TypeLits
import Data.Proxy
import qualified Data.Set as S

import SPL.Compiler.Parser.Testable ()
import SPL.Compiler.Common.Testable
import SPL.Compiler.Parser.AST
import SPL.Compiler.SemanticAnalysis.Core (CoreType(..), TCon(..), TCon'(..), Subst(..))
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import SPL.Compiler.SemanticAnalysis.CoreEntityLocation
import SPL.Compiler.CodeGen.IRLang (type (-->))

-- instance Testable CoreIdentifier where
--     toTestForm (CoreIdentifier _ i) = CoreIdentifier def i

-- instance Testable ASTFunCall where
--     toTestForm (ASTFunCall _ i t e) = 
--         ASTFunCall def (toTestForm i) (toTestForm t) (toTestForm e)

instance Testable CoreType where
    toTestForm (CoreFunType _ c t1 t2) = CoreFunType def (toTestForm c) (toTestForm t1) (toTestForm t2)
    toTestForm (CoreTupleType _ t1 t2) = CoreTupleType def (toTestForm t1) (toTestForm t2)
    toTestForm (CoreListType _ t) = CoreListType def (toTestForm t)
    toTestForm (CoreVarType _ v) = CoreVarType def v
    toTestForm (CoreIntType _) = CoreIntType def
    toTestForm (CoreBoolType _) = CoreBoolType def
    toTestForm (CoreCharType _) = CoreCharType def
    toTestForm (CoreVoidType _) = CoreVoidType def

-- instance Testable ASTExpr where
--     toTestForm (TupExpr _ p1 p2) = TupExpr def (toTestForm p1) (toTestForm p2)
--     toTestForm (FunCallExpr c) = FunCallExpr (toTestForm c)
--     toTestForm (VarIdentifierExpr i) = VarIdentifierExpr (toTestForm i)
--     toTestForm (FunIdentifierExpr i) = FunIdentifierExpr (toTestForm i)
--     toTestForm (IntExpr _ i) = IntExpr def i
--     toTestForm (CharExpr _ c) = CharExpr def c
--     toTestForm (BoolExpr _ b) = BoolExpr def b
--     toTestForm (OpExpr _ o e) = OpExpr def o (toTestForm e)
--     toTestForm (Op2Expr _ e1 o e2) = Op2Expr def (toTestForm e1) o (toTestForm e2)
--     toTestForm (EmptyListExpr _ t) = EmptyListExpr def (toTestForm t)

-- instance Testable ASTVarDecl where
--     toTestForm (ASTVarDecl _ t i e) = ASTVarDecl def (toTestForm t) (toTestForm i) (toTestForm e)

-- instance Testable ASTFunDecl where
--     toTestForm (ASTFunDecl _ i is t b) =
--         ASTFunDecl def (toTestForm i) (toTestForm is) (toTestForm t) (toTestForm b)

instance Testable TCon where
    toTestForm (TEq tt) = TEq (toTestForm tt)
    toTestForm (TOrd tt) = TOrd (toTestForm tt)
    toTestForm (TPrint tt) = TPrint (toTestForm tt)

-- instance Testable CoreFunBody where
--     toTestForm (CoreFunBody _ v s) = CoreFunBody def (toTestForm v) (toTestForm s)

-- instance Testable ASTStmt where
--     toTestForm (IfElseStmt _ val1 val2 val3) = IfElseStmt def (toTestForm val1) (toTestForm val2) (toTestForm val3)
--     toTestForm (WhileStmt _ val1 val2) = WhileStmt def (toTestForm val1) (toTestForm val2)
--     toTestForm (AssignStmt _ id fds t e) = AssignStmt def (toTestForm id) (toTestForm fds) (toTestForm t) (toTestForm e)
--     toTestForm (FunCallStmt val1) = FunCallStmt (toTestForm val1)
--     toTestForm (ReturnStmt _ val1) = ReturnStmt def (toTestForm val1)

instance Testable Subst where
    toTestForm (Subst var) = Subst $ toTestForm <$> var

class ToExpr a where
    expr :: a -> ASTExpr

data Nop

instance ToExpr Nop where
    expr = undefined

instance ToExpr Int where
    expr i = IntExpr def (fromIntegral i)

instance ToExpr Bool where
    expr b = BoolExpr def b

instance ToExpr Char where
    expr c = CharExpr def c

instance ToExpr ASTExpr where
    expr e = e

instance ToExpr a => ToExpr [a] where
    expr [] = EmptyListExpr def
    expr (x:xs) = Op2Expr def (expr x) Cons (expr xs)

instance (ToExpr a, ToExpr b) => ToExpr (a,b) where
    expr (a,b) = TupExpr def (expr a) (expr b)

instance ToExpr ASTFunCall where
    expr f = FunCallExpr f

fun1 :: ToExpr a => Text -> a -> ASTFunCall
fun1 id e = ASTFunCall def (IdentifierExpr $ ASTIdentifier def id) [expr e]

fun2 :: (ToExpr a, ToExpr b) => Text -> a -> b -> ASTFunCall
fun2 id e1 e2 = ASTFunCall def (IdentifierExpr $ ASTIdentifier def id) [expr e1, expr e2]

fun3 :: (ToExpr a, ToExpr b, ToExpr c) => Text -> a -> b -> c -> ASTFunCall
fun3 id e1 e2 e3 = ASTFunCall def (IdentifierExpr $ ASTIdentifier def id) [expr e1, expr e2, expr e3]

op1 :: (ToExpr a) => OpUnary -> a -> ASTExpr
op1 op e = OpExpr def op (expr e)

op2 :: (ToExpr a, ToExpr b) => a -> OpBin -> b -> ASTExpr
op2 e1 op e2 = Op2Expr def (expr e1) op (expr e2)

ident = ASTIdentifier def

iexpr = expr @Int

emptyList :: ASTExpr
emptyList = EmptyListExpr def

class ToType a where
    toType :: Proxy a -> CoreType

instance ToType Int where
    toType _ = CoreIntType def

instance ToType Bool where
    toType _ = CoreBoolType def

instance ToType Char where
    toType _ = CoreCharType def

instance KnownSymbol a => ToType (TVar (a :: Symbol)) where
    toType p = CoreVarType def (T.pack . symbolVal $ Proxy @a)

instance ToType a => ToType [a] where
    toType _ = CoreListType def (toType (Proxy @a))

instance (ToType a, ToType b) => ToType (a,b) where
    toType _ = CoreTupleType def (toType (Proxy @a)) (toType (Proxy @b))

instance (ToType b) => ToType ((-->) '[] b) where
    toType _ = CoreFunType def [] [] (toType (Proxy @b))

instance (ToType a, ToType b) => ToType ((-->) (a ': '[]) b) where
    toType _ = CoreFunType def [] [toType (Proxy @a)] (toType (Proxy @b))

instance (ToType a, ToType aa, ToType b) => ToType ((-->) (a ': aa ': '[]) b) where
    toType _ = CoreFunType def [] [toType (Proxy @a), toType (Proxy @aa)] (toType (Proxy @b))

instance (ToType a, ToType aa, ToType aaa, ToType b) => ToType ((-->) (a ': aa ': aaa ': '[]) b) where
    toType _ = CoreFunType def [] [toType (Proxy @a), toType (Proxy @aa), toType (Proxy @aaa)] (toType (Proxy @b))

data TVar a = TVar

typ :: forall a. ToType a => CoreType
typ = toType (Proxy :: Proxy a)

class ToStmt a where
    stmt :: a -> ASTStmt

instance ToStmt ASTStmt where
    stmt = id

instance ToStmt ASTFunCall where
    stmt = FunCallStmt

fd :: Text -> [Field] -> ASTExpr
fd id = FieldSelectExpr def (IdentifierExpr $ ASTIdentifier def id)

ite :: ToExpr a => a -> [ASTStmt] -> [ASTStmt] -> ASTStmt
ite c = IfElseStmt def (expr c)

while :: ToExpr a => a -> [ASTStmt] -> ASTStmt
while c = WhileStmt def (expr c)

infixl 2 =:

(=:) :: ToExpr a => (Text, [Field]) -> a -> ASTStmt
(=:) (id, fd) x = AssignStmt def (ident id) fd (expr x)

ret :: ToExpr a => a -> ASTStmt
ret a = ReturnStmt def (Just . expr $ a)

retVoid :: ASTStmt
retVoid = ReturnStmt def Nothing

defineI :: Text -> ASTExpr -> ASTVarDecl
defineI id  = ASTVarDecl def (ASTUnknownType def) (ASTIdentifier def id)

define :: Text -> ASTType -> ASTExpr -> ASTVarDecl
define id t = ASTVarDecl def t (ASTIdentifier def id)

declare :: Text -> [Text] -> [ASTVarDecl] -> [ASTStmt] -> ASTFunDecl
declare id args vs stmt =
    ASTFunDecl def
        (ASTIdentifier def id)
        (map (ASTIdentifier def) args)
        (ASTUnknownType def)
        (ASTFunBody def vs stmt)
