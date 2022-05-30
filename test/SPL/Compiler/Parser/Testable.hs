module SPL.Compiler.Parser.Testable where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..), Type(..), Keyword(..))
import SPL.Compiler.Parser.AST
import SPL.Compiler.Parser.ASTEntityLocation
import SPL.Compiler.Common.Testable
import Data.Default

instance Testable ASTIdentifier where
    toTestForm (ASTIdentifier _ i) = ASTIdentifier def i

instance Testable ASTFunCall where
    toTestForm (ASTFunCall _ i e) = ASTFunCall def (toTestForm i) (toTestForm e)

instance Testable ASTType where
    toTestForm (ASTUnknownType l) = ASTUnknownType def
    toTestForm (ASTFunType _ t r) = ASTFunType def (toTestForm t) (toTestForm r)
    toTestForm (ASTTupleType _ t1 t2) = ASTTupleType def (toTestForm t1) (toTestForm t2)
    toTestForm (ASTListType _ t) = ASTListType def (toTestForm t)
    toTestForm (ASTVarType _ v) = ASTVarType def v
    toTestForm (ASTIntType _) = ASTIntType def
    toTestForm (ASTBoolType _) = ASTBoolType def
    toTestForm (ASTCharType _) = ASTCharType def
    toTestForm (ASTVoidType _) = ASTVoidType def

instance Testable Field where
    toTestForm (Hd _) = Hd def
    toTestForm (Tl _) = Tl def
    toTestForm (Fst _) = Fst def
    toTestForm (Snd _) = Snd def

instance Testable ASTExpr where
    toTestForm (TupExpr _ p1 p2) = TupExpr def (toTestForm p1) (toTestForm p2)
    toTestForm (FunCallExpr c) = FunCallExpr (toTestForm c)
    toTestForm (IdentifierExpr i) = IdentifierExpr (toTestForm i)
    toTestForm (FieldSelectExpr _ e fds) = FieldSelectExpr def (toTestForm e) (toTestForm fds)
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

instance Testable ASTStmt where
    toTestForm (IfElseStmt _ val1 val2 val3) = IfElseStmt def (toTestForm val1) (toTestForm val2) (toTestForm val3)
    toTestForm (WhileStmt _ val1 val2) = WhileStmt def (toTestForm val1) (toTestForm val2)
    toTestForm (AssignStmt _ id fds e) = AssignStmt def (toTestForm id) (toTestForm fds) (toTestForm e)
    toTestForm (FunCallStmt val1) = FunCallStmt (toTestForm val1)
    toTestForm (ReturnStmt _ val1) = ReturnStmt def (toTestForm val1)
