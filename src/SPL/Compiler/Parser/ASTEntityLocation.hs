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

instance Locatable ASTField where
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

instance Locatable ASTFieldSelector where
    setLoc l (ASTFieldSelector _ f x) = ASTFieldSelector l f x
    getLoc (ASTFieldSelector l _ _) = l

instance Locatable ASTExpr where
    setLoc l (FieldSelectExpr f) = FieldSelectExpr (setLoc l f)
    setLoc l (IntExpr _ i) = IntExpr l i
    setLoc l (CharExpr _ c) = CharExpr l c
    setLoc l (BoolExpr _ b) = BoolExpr l b
    setLoc l (FunCallExpr (ASTFunCall _ f x)) = FunCallExpr (ASTFunCall l f x)
    setLoc l (OpExpr _ o a) = OpExpr l o a 
    setLoc l (Op2Expr _ o a b) = Op2Expr l o a b
    setLoc l (EmptyListExpr _) = EmptyListExpr l
    setLoc l (TupExpr _ a b) = TupExpr l a b
    getLoc (FieldSelectExpr f) = getLoc f
    getLoc (IntExpr l _) = l
    getLoc (CharExpr l _) = l
    getLoc (BoolExpr l _) = l
    getLoc (FunCallExpr (ASTFunCall l _ _)) = l
    getLoc (OpExpr l _ _) = l 
    getLoc (Op2Expr l _ _ _) = l  
    getLoc (EmptyListExpr l) = l
    getLoc (TupExpr l _ _) = l

instance Locatable ASTStmt where
    setLoc l (IfElseStmt _ c a b) = IfElseStmt l c a b
    setLoc l (WhileStmt _ c b) = WhileStmt l c b
    setLoc l (AssignStmt _ v r) = AssignStmt l v r
    setLoc l (FunCallStmt _ f) = FunCallStmt l f
    setLoc l (ReturnStmt _ r) = ReturnStmt l r
    getLoc (IfElseStmt l _ _ _) = l
    getLoc (WhileStmt l _ _) = l
    getLoc (AssignStmt l _ _) = l
    getLoc (FunCallStmt l _) = l
    getLoc (ReturnStmt l _) = l
    
instance Locatable ASTType where
    setLoc l (ASTUnknownType _) = ASTUnknownType l
    setLoc l (ASTFunType _ f) = ASTFunType l f
    setLoc l (ASTTupleType _ a b) = ASTTupleType l a b
    setLoc l (ASTListType _ x) = ASTListType l x
    setLoc l (ASTVarType _ x) = ASTVarType l x
    setLoc l (ASTIntType _) = ASTIntType l
    setLoc l (ASTBoolType _) = ASTBoolType l
    setLoc l (ASTCharType _) = ASTCharType l
    setLoc l (ASTVoidType _) = ASTVoidType l
    getLoc (ASTUnknownType l) = l
    getLoc (ASTFunType l _) = l
    getLoc (ASTTupleType l _ _) = l
    getLoc (ASTListType l _) = l
    getLoc (ASTVarType l _) = l
    getLoc (ASTIntType l) = l
    getLoc (ASTBoolType l) = l
    getLoc (ASTCharType l) = l
    getLoc (ASTVoidType l) = l

instance Locatable ASTFunBody where
    setLoc l (ASTFunBody _ d b) = ASTFunBody l d b
    getLoc (ASTFunBody l _ _) = l
