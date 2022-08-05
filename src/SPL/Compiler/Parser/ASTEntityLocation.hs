module SPL.Compiler.Parser.ASTEntityLocation where

import SPL.Compiler.Parser.AST
import SPL.Compiler.Common.EntityLocation
import qualified Data.Text as T
import Control.Lens ((^.), _Just)

instance Locatable ASTIdentifier where
    setLoc l (ASTIdentifier _ v) = ASTIdentifier l v
    getLoc (ASTIdentifier l _) = l

instance Locatable ASTFunCall where
    setLoc l (ASTFunCall _ f r) = ASTFunCall l f r
    getLoc (ASTFunCall l _ _) = l

instance Locatable Field where
    setLoc l (Hd _) = Hd l
    setLoc l (Tl _) = Tl l
    setLoc l (Fst _) = Fst l
    setLoc l (Snd _) = Snd l
    getLoc (Hd l) = l
    getLoc (Tl l) = l
    getLoc (Fst l) = l
    getLoc (Snd l) = l

instance Locatable ASTVarDecl where
    setLoc l (ASTVarDecl _ t i e) = ASTVarDecl l t i e
    getLoc (ASTVarDecl l _ _ _) = l

instance Locatable ASTExpr where
    setLoc l (IdentifierExpr i) = IdentifierExpr (setLoc l i)
    setLoc l (IntExpr _ i) = IntExpr l i
    setLoc l (CharExpr _ c) = CharExpr l c
    setLoc l (BoolExpr _ b) = BoolExpr l b
    setLoc l (FieldSelectExpr _ e fd) = FieldSelectExpr l e fd
    setLoc l (FunCallExpr (ASTFunCall _ f x)) = FunCallExpr (ASTFunCall l f x)
    setLoc l (OpExpr _ o a) = OpExpr l o a 
    setLoc l (Op2Expr _ o a b) = Op2Expr l o a b
    setLoc l (EmptyListExpr _) = EmptyListExpr l
    setLoc l (EmptyCharListExpr _) = EmptyCharListExpr l
    setLoc l (TupExpr _ a b) = TupExpr l a b
    getLoc (IdentifierExpr i) = getLoc i
    getLoc (FieldSelectExpr l _ _) = l
    getLoc (IntExpr l _) = l
    getLoc (CharExpr l _) = l
    getLoc (BoolExpr l _) = l
    getLoc (FunCallExpr (ASTFunCall l _ _)) = l
    getLoc (OpExpr l _ _) = l 
    getLoc (Op2Expr l _ _ _) = l  
    getLoc (EmptyListExpr l) = l
    getLoc (EmptyCharListExpr l) = l
    getLoc (TupExpr l _ _) = l

instance Locatable ASTStmt where
    setLoc l (IfElseStmt _ c a b) = IfElseStmt l c a b
    setLoc l (WhileStmt _ c b) = WhileStmt l c b
    setLoc l (VarDeclStmt v) = VarDeclStmt (setLoc l v)
    setLoc l (AssignStmt _ v fd r) = AssignStmt l v fd r
    setLoc l (FunCallStmt f) = FunCallStmt (setLoc l f)
    setLoc l (ReturnStmt _ r) = ReturnStmt l r
    getLoc (IfElseStmt l _ _ _) = l
    getLoc (WhileStmt l _ _) = l
    getLoc (VarDeclStmt v) = getLoc v
    getLoc (AssignStmt l _ _ _) = l
    getLoc (FunCallStmt f) = getLoc f
    getLoc (ReturnStmt l _) = l
    
instance Locatable ASTType where
    setLoc l (ASTUnknownType _) = ASTUnknownType l
    setLoc l (ASTFunType _ a r) = ASTFunType l a r
    setLoc l (ASTTupleType _ a b) = ASTTupleType l a b
    setLoc l (ASTListType _ x) = ASTListType l x
    setLoc l (ASTVarType _ x) = ASTVarType l x
    setLoc l (ASTIntType _) = ASTIntType l
    setLoc l (ASTBoolType _) = ASTBoolType l
    setLoc l (ASTCharType _) = ASTCharType l
    setLoc l (ASTVoidType _) = ASTVoidType l
    getLoc (ASTUnknownType l) = l
    getLoc (ASTFunType l _ _) = l
    getLoc (ASTTupleType l _ _) = l
    getLoc (ASTListType l _) = l
    getLoc (ASTVarType l _) = l
    getLoc (ASTIntType l) = l
    getLoc (ASTBoolType l) = l
    getLoc (ASTCharType l) = l
    getLoc (ASTVoidType l) = l

instance Locatable ASTFunBody where
    setLoc l (ASTFunBody _ b) = ASTFunBody l b
    getLoc (ASTFunBody l _) = l
