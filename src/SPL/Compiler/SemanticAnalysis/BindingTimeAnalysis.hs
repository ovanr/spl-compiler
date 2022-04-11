
module SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis where

import SPL.Compiler.SemanticAnalysis.TCT
import qualified Data.List as L

optimize :: TCT -> TCT
optimize (TCT leafs) = TCT $ map optimize' leafs
    where
        optimize' (TCTVar v) = TCTVar $ optimizeVarDecl v
        optimize' (TCTFun f) = TCTFun $ optimizeFunDecl f

optimizeVarDecl :: TCTVarDecl -> TCTVarDecl
optimizeVarDecl (TCTVarDecl l t id e) = TCTVarDecl l t id (optimizeExpr e)

optimizeFunDecl :: TCTFunDecl -> TCTFunDecl
optimizeFunDecl (TCTFunDecl l id args t (TCTFunBody lb vars stmts)) =
    TCTFunDecl l id args t $ 
        TCTFunBody lb (map optimizeVarDecl vars) (concatMap optimizeStmt stmts)

optimizeStmt :: TCTStmt -> [TCTStmt]
optimizeStmt (IfElseStmt l e taken nTaken) =
    case optimizeExpr e of
        (BoolExpr _ True) -> elimUnreachableStmt $ concatMap optimizeStmt taken
        (BoolExpr _ False) -> elimUnreachableStmt $ concatMap optimizeStmt nTaken
        e' -> [IfElseStmt l e' (elimUnreachableStmt $ concatMap optimizeStmt taken) 
                               (elimUnreachableStmt $ concatMap optimizeStmt nTaken)]
optimizeStmt (WhileStmt l e stmts) =
    case optimizeExpr e of
        (BoolExpr _ False) -> []
        e' -> [WhileStmt l e' (elimUnreachableStmt $ concatMap optimizeStmt stmts)]
optimizeStmt (AssignStmt l fd e) = [AssignStmt l fd (optimizeExpr e)]
optimizeStmt (FunCallStmt l f) = [FunCallStmt l (optimizeFunCall f)]
optimizeStmt (ReturnStmt l e) = [ReturnStmt l (optimizeExpr <$> e)]

syntaxEqFieldSelectors :: TCTFieldSelector -> TCTFieldSelector -> Bool
syntaxEqFieldSelectors (TCTFieldSelector _ id1 fd1) (TCTFieldSelector _ id2 fd2)
    | id1 == id2 = and $ zipWith (==) fd1 fd2
    | otherwise = False

elimUnreachableStmt :: [TCTStmt] -> [TCTStmt]
elimUnreachableStmt xs =
    maybe xs (const $ L.dropWhileEnd (not . isReturn) xs) (L.find isReturn xs)
    where
        isReturn (ReturnStmt _ _) = True
        isReturn _ = False

optimizeExpr :: TCTExpr -> TCTExpr
optimizeExpr e@(Op2Expr l e1 op e2) =
    case (optimizeExpr e1, optimizeExpr e2, op) of
        (IntExpr _ i1, IntExpr _ i2, _) -> evaluateI l i1 op i2
        (CharExpr _ b1, CharExpr _ b2, _) -> evaluateC l b1 op b2
        (BoolExpr _ c1, BoolExpr _ c2, _) -> evaluateB l c1 op c2
        (eb@(BoolExpr _ True), _, LogOr) -> eb
        (eb@(BoolExpr _ False), _, LogAnd) -> eb
        (FieldSelectExpr f1, FieldSelectExpr f2, Equal) ->
            if syntaxEqFieldSelectors f1 f2 then
                BoolExpr l True
            else
                e
        (FieldSelectExpr f1, FieldSelectExpr f2, Nequal) ->
            if syntaxEqFieldSelectors f1 f2 then
                BoolExpr l False
            else
                e
        (e1', e2', _) -> Op2Expr l e1' op e2'

optimizeExpr (OpExpr l op1 e) =
    case (optimizeExpr e, op1) of
        (IntExpr _ i, UnMinus) -> IntExpr l (-i)
        (BoolExpr _ i, UnNeg) -> BoolExpr l (not i)
        (e', _) -> OpExpr l op1 e'

optimizeExpr (TupExpr l e1 e2) = TupExpr l (optimizeExpr e1) (optimizeExpr e2)
optimizeExpr (FunCallExpr f) = FunCallExpr (optimizeFunCall f)
optimizeExpr e = e

optimizeFunCall :: TCTFunCall -> TCTFunCall
optimizeFunCall (TCTFunCall l name args) = TCTFunCall l name (map optimizeExpr args)

evaluateI :: EntityLoc -> Integer -> OpBin -> Integer -> TCTExpr
evaluateI l i1 op i2 =
        case op of
            Plus -> IntExpr l (i1 + i2)
            Minus -> IntExpr l (i1 - i2)
            Mul  -> IntExpr l (i1 * i2)
            Div -> IntExpr l (i1 `div` i2)
            Mod -> IntExpr l (i1 `mod` i2)
            Pow -> IntExpr l (i1 ^ i2)
            Equal -> BoolExpr l (i1 == i2)
            Less -> BoolExpr l (i1 < i2)
            Greater -> BoolExpr l (i1 > i2)
            LessEq -> BoolExpr l (i1 <= i2)
            GreaterEq -> BoolExpr l (i1 >= i2)
            Nequal -> BoolExpr l (i1 /= i2)
            _ -> error "internal optimization error: pattern should not occur"

evaluateC :: EntityLoc -> Char -> OpBin -> Char -> TCTExpr
evaluateC l c1 op c2 =
        case op of
            Equal -> BoolExpr l (c1 == c2)
            Less -> BoolExpr l (c1 < c2)
            Greater -> BoolExpr l (c1 > c2)
            LessEq -> BoolExpr l (c1 <= c2)
            GreaterEq -> BoolExpr l (c1 >= c2)
            Nequal -> BoolExpr l (c1 /= c2)
            _ -> error "internal optimization error: pattern should not occur"

evaluateB :: EntityLoc -> Bool -> OpBin -> Bool -> TCTExpr
evaluateB l b1 op b2 =
        case op of
            Equal -> BoolExpr l (b1 == b2)
            Less -> BoolExpr l (b1 < b2)
            Greater -> BoolExpr l (b1 > b2)
            LessEq -> BoolExpr l (b1 <= b2)
            GreaterEq -> BoolExpr l (b1 >= b2)
            Nequal -> BoolExpr l (b1 /= b2)
            LogAnd -> BoolExpr l (b1 && b2)
            LogOr -> BoolExpr l (b1 || b2)
            _ -> error "internal optimization error: pattern should not occur"
