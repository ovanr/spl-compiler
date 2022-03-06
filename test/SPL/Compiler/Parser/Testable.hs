module SPL.Compiler.Parser.Testable where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..), Type(..), Keyword(..))
import SPL.Compiler.Parser.AST
import SPL.Compiler.Parser.ASTEntityLocation
import Data.Default

instance Default EntityLoc where
    def = EntityLoc (1,1) (1,1)

instance Default AlexPosn where
    def = AlexPn 0 1 1

-- used for test purposes
-- transform a data type to its test form
-- this means that certain fields may be replaced
-- with their default values for ease of comparisons, etc.
class Testable a where
    toTestForm :: a -> a

instance Testable ASTIdentifier where
    toTestForm (ASTIdentifier _ i) = ASTIdentifier def i

instance Testable ASTFunCall where
    toTestForm (ASTFunCall _ i e) = ASTFunCall def (toTestForm i) (toTestForm e)

instance Testable ASTType where
    toTestForm (ASTUnknownType l) = ASTUnknownType def
    toTestForm (ASTFunType _ t) = ASTFunType def (toTestForm t)
    toTestForm (ASTTupleType _ t1 t2) = ASTTupleType def (toTestForm t1) (toTestForm t2)
    toTestForm (ASTListType _ t) = ASTListType def (toTestForm t)
    toTestForm (ASTVarType _ v) = ASTVarType def v
    toTestForm (ASTIntType _) = ASTIntType def
    toTestForm (ASTBoolType _) = ASTBoolType def
    toTestForm (ASTCharType _) = ASTCharType def
    toTestForm (ASTVoidType _) = ASTVoidType def

instance Testable ASTField where
    toTestForm (Hd _) = Hd def
    toTestForm (Tl _) = Tl def
    toTestForm (Fst _) = Fst def
    toTestForm (Snd _) = Snd def

instance Testable ASTFieldSelector where
    toTestForm (ASTFieldSelector _ i fs) = ASTFieldSelector def (toTestForm i) (toTestForm fs)

instance Testable ASTExpr where
    toTestForm (TupExpr _ p1 p2) = TupExpr def (toTestForm p1) (toTestForm p2)
    toTestForm (FunCallExpr c) = FunCallExpr (toTestForm c)
    toTestForm (FieldSelectExpr i) = FieldSelectExpr (toTestForm i)
    toTestForm (IntExpr _ i) = IntExpr def i
    toTestForm (CharExpr _ c) = CharExpr def c
    toTestForm (BoolExpr _ b) = BoolExpr def b
    toTestForm (OpExpr _ o e) = OpExpr def o (toTestForm e)
    toTestForm (Op2Expr _ e1 o e2) = Op2Expr def (toTestForm e1) o (toTestForm e2)
    toTestForm (EmptyListExpr _ ) = EmptyListExpr def

instance Testable ASTVarDecl where
    toTestForm (ASTVarDecl _ t i e) = ASTVarDecl def (toTestForm t) (toTestForm i) (toTestForm e)

instance Testable ASTFunDecl where 
    toTestForm (ASTFunDecl _ i is t b) =
        ASTFunDecl def (toTestForm i) (toTestForm is) (toTestForm t) (toTestForm b)

instance Testable ASTFunBody where
    toTestForm (ASTFunBody _ v s) = ASTFunBody def (toTestForm v) (toTestForm s)

instance Testable a => Testable [a] where
    toTestForm = map toTestForm

instance Testable ASTStmt where
    toTestForm (IfElseStmt _ val1 val2 val3) = IfElseStmt def (toTestForm val1) (toTestForm val2) (toTestForm val3)
    toTestForm (WhileStmt _ val1 val2) = WhileStmt def (toTestForm val1) (toTestForm val2)
    toTestForm (AssignStmt _ val1 val2) = AssignStmt def (toTestForm val1) (toTestForm val2)
    toTestForm (FunCallStmt _ val1) = FunCallStmt def (toTestForm val1)
    toTestForm (ReturnStmt _ val1) = ReturnStmt def (toTestForm val1)

instance Testable a => Testable (Maybe a) where
    toTestForm (Just val) = Just (toTestForm val)
    toTestForm Nothing = Nothing