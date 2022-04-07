module SPL.Compiler.TypeChecker.Testable where

import Data.Default
import Data.Text (Text)
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
    toExpr :: a -> TCTExpr

data Unknown

instance ToExpr Unknown where
    toExpr = undefined

instance ToExpr Int where
    toExpr i = IntExpr def (fromIntegral i)

instance ToExpr Bool where
    toExpr b = BoolExpr def b

instance ToExpr Char where
    toExpr c = CharExpr def c

instance ToExpr TCTExpr where
    toExpr e = e

instance ToExpr a => ToExpr [a] where
    toExpr [] = EmptyListExpr def
    toExpr (x:xs) = Op2Expr def (toExpr x) Cons (toExpr xs)

instance (ToExpr a, ToExpr b) => ToExpr (a,b) where
    toExpr (a,b) = TupExpr def (toExpr a) (toExpr b)

class ToType a where
    toType :: a -> TCTType

instance ToType Int where
    toType i = TCTIntType def 

instance ToType Bool where
    toType b = TCTBoolType def

instance ToType Char where
    toType c = TCTCharType def

instance ToType Text where
    toType name = TCTVarType def name

instance ToType TCTType where
    toType t = t

instance ToType a => ToType [a] where
    toType [x] = TCTListType def (toType x)
    toType _ = undefined

instance (ToType a, ToType b) => ToType (a,b) where
    toType (a,b) = TCTTupleType def (toType a) (toType b)

