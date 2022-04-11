module SPL.Compiler.SemanticAnalysis.TCTEntityLocation where

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.SemanticAnalysis.TCT

instance Locatable TCTIdentifier where
    setLoc l (TCTIdentifier _ v) = TCTIdentifier l v
    getLoc (TCTIdentifier l _) = l

instance Locatable TCTFunCall where
    setLoc l (TCTFunCall _ f r) = TCTFunCall l f r
    getLoc (TCTFunCall l _ _) = l

instance Locatable TCTField where
    setLoc l (Hd _) = Hd l
    setLoc l (Tl _) = Tl l
    setLoc l (Fst _) = Fst l
    setLoc l (Snd _) = Snd l
    getLoc (Hd l) = l
    getLoc (Tl l) = l
    getLoc (Fst l) = l
    getLoc (Snd l) = l

instance Locatable TCTVarDecl where
    setLoc l (TCTVarDecl _ t i e) = TCTVarDecl l t i e
    getLoc (TCTVarDecl l _ _ _) = l

instance Locatable TCTFieldSelector where
    setLoc l (TCTFieldSelector _ f x) = TCTFieldSelector l f x
    getLoc (TCTFieldSelector l _ _) = l

instance Locatable TCTExpr where
    setLoc l (FieldSelectExpr f) = FieldSelectExpr (setLoc l f)
    setLoc l (IntExpr _ i) = IntExpr l i
    setLoc l (CharExpr _ c) = CharExpr l c
    setLoc l (BoolExpr _ b) = BoolExpr l b
    setLoc l (FunCallExpr (TCTFunCall _ f x)) = FunCallExpr (TCTFunCall l f x)
    setLoc l (OpExpr _ o a) = OpExpr l o a 
    setLoc l (Op2Expr _ o a b) = Op2Expr l o a b
    setLoc l (EmptyListExpr _) = EmptyListExpr l
    setLoc l (TupExpr _ a b) = TupExpr l a b
    getLoc (FieldSelectExpr f) = getLoc f
    getLoc (IntExpr l _) = l
    getLoc (CharExpr l _) = l
    getLoc (BoolExpr l _) = l
    getLoc (FunCallExpr (TCTFunCall l _ _)) = l
    getLoc (OpExpr l _ _) = l 
    getLoc (Op2Expr l _ _ _) = l  
    getLoc (EmptyListExpr l) = l
    getLoc (TupExpr l _ _) = l

instance Locatable TCTStmt where
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
    
instance Locatable TCTType where
    setLoc l (TCTFunType _ c a b) = TCTFunType l c a b
    setLoc l (TCTTupleType _ a b) = TCTTupleType l a b
    setLoc l (TCTListType _ x) = TCTListType l x
    setLoc l (TCTVarType _ x) = TCTVarType l x
    setLoc l (TCTIntType _) = TCTIntType l
    setLoc l (TCTBoolType _) = TCTBoolType l
    setLoc l (TCTCharType _) = TCTCharType l
    setLoc l (TCTVoidType _) = TCTVoidType l
    getLoc (TCTFunType l _ _ _) = l
    getLoc (TCTTupleType l _ _) = l
    getLoc (TCTListType l _) = l
    getLoc (TCTVarType l _) = l
    getLoc (TCTIntType l) = l
    getLoc (TCTBoolType l) = l
    getLoc (TCTCharType l) = l
    getLoc (TCTVoidType l) = l

instance Locatable TCon where
    setLoc l (TEq t) = TEq $ setLoc l t
    setLoc l (TOrd t) = TOrd $ setLoc l t
    setLoc l (TPrint t) = TPrint $ setLoc l t
    getLoc (TEq t) = getLoc t
    getLoc (TOrd t) = getLoc t
    getLoc (TPrint t) = getLoc t

instance Locatable TCTFunBody where
    setLoc l (TCTFunBody _ d b) = TCTFunBody l d b
    getLoc (TCTFunBody l _ _) = l
