{-# LANGUAGE FlexibleInstances #-}
module SPL.Compiler.SemanticAnalysis.CoreEntityLocation where

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.Parser.ASTEntityLocation ()

instance Locatable CoreIdentifier where
    setLoc l (CoreIdentifier _ v) = CoreIdentifier l v
    getLoc (CoreIdentifier l _) = l

instance Locatable CoreFunCall where
    setLoc l (CoreFunCall _ f t xs) = CoreFunCall l f t xs
    getLoc (CoreFunCall l _ _ _) = l

instance Locatable CoreVarDecl where
    setLoc l (CoreVarDecl _ t i e) = CoreVarDecl l t i e
    getLoc (CoreVarDecl l _ _ _) = l

instance Locatable CoreFunDecl where
    setLoc l (CoreFunDecl _ id args t body) = CoreFunDecl l id args t body
    getLoc (CoreFunDecl l _ _ _ _) = l

instance Locatable CoreExpr where
    setLoc l (IntExpr _ i) = IntExpr l i
    setLoc l (CharExpr _ c) = CharExpr l c
    setLoc l (BoolExpr _ b) = BoolExpr l b
    setLoc l (VarIdentifierExpr b) = VarIdentifierExpr (setLoc l b)
    setLoc l (FunIdentifierExpr t b) = FunIdentifierExpr t (setLoc l b)
    setLoc l (FunCallExpr f) = FunCallExpr (setLoc l f)
    setLoc l (OpExpr _ o a) = OpExpr l o a 
    setLoc l (Op2Expr _ e1 t1 op e2 t2) = Op2Expr l e1 t1 op e2 t2
    setLoc l (EmptyListExpr _ t) = EmptyListExpr l t
    setLoc l (TupExpr _ a b) = TupExpr l a b
    getLoc (IntExpr l _) = l
    getLoc (CharExpr l _) = l
    getLoc (BoolExpr l _) = l
    getLoc (VarIdentifierExpr i) = getLoc i
    getLoc (FunIdentifierExpr i t) = getLoc i
    getLoc (FunCallExpr f) = getLoc f
    getLoc (OpExpr l _ _) = l 
    getLoc (Op2Expr l _ _ _ _ _) = l  
    getLoc (EmptyListExpr l _) = l
    getLoc (TupExpr l _ _) = l

instance Locatable CoreStmt where
    setLoc l (IfElseStmt _ c a b) = IfElseStmt l c a b
    setLoc l (WhileStmt _ c b) = WhileStmt l c b
    setLoc l (AssignStmt _ i fd t v) = AssignStmt l i fd t v
    setLoc l (FunCallStmt f) = FunCallStmt (setLoc l f)
    setLoc l (ReturnStmt _ r) = ReturnStmt l r
    getLoc (IfElseStmt l _ _ _) = l
    getLoc (WhileStmt l _ _) = l
    getLoc (AssignStmt l _ _ _ _) = l
    getLoc (FunCallStmt f) = getLoc f
    getLoc (ReturnStmt l _) = l
    
instance Locatable CoreType where
    setLoc l (CoreFunType _ a b) = CoreFunType l a b
    setLoc l (CoreTupleType _ a b) = CoreTupleType l a b
    setLoc l (CoreListType _ x) = CoreListType l x
    setLoc l (CoreVarType _ x) = CoreVarType l x
    setLoc l (CoreIntType _) = CoreIntType l
    setLoc l (CoreBoolType _) = CoreBoolType l
    setLoc l (CoreCharType _) = CoreCharType l
    setLoc l (CoreVoidType _) = CoreVoidType l 
    getLoc (CoreFunType l _ _) = l
    getLoc (CoreTupleType l _ _) = l
    getLoc (CoreListType l _) = l
    getLoc (CoreVarType l _) = l
    getLoc (CoreIntType l) = l
    getLoc (CoreBoolType l) = l
    getLoc (CoreCharType l) = l
    getLoc (CoreVoidType l) = l

instance Locatable TCon where
    setLoc l (TEq t) = TEq $ setLoc l t
    setLoc l (TOrd t) = TOrd $ setLoc l t
    setLoc l (TPrint t) = TPrint $ setLoc l t
    getLoc (TEq t) = getLoc t
    getLoc (TOrd t) = getLoc t
    getLoc (TPrint t) = getLoc t

instance Locatable CoreFunBody where
    setLoc l (CoreFunBody _ v s) = CoreFunBody l v s
    getLoc (CoreFunBody l _ _) = l
