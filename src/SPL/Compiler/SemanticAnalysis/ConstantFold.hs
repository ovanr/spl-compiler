
module SPL.Compiler.SemanticAnalysis.ConstantFold (
    constantFold
    ) where

import SPL.Compiler.SemanticAnalysis.Core
import qualified Data.List as L
import Data.Bifunctor (Bifunctor(bimap))

constantFold :: Core -> Core
constantFold (Core varDecls funDecls) = 
    Core (map optimizeVarDecl varDecls)
         (map (fmap optimizeFunDecl) funDecls)

optimizeVarDecl :: CoreVarDecl -> CoreVarDecl
optimizeVarDecl (CoreVarDecl l t id e) = CoreVarDecl l t id (optimizeExpr e)

optimizeFunDecl :: CoreFunDecl -> CoreFunDecl
optimizeFunDecl (CoreFunDecl l id args t (CoreFunBody lb stmts)) =
    CoreFunDecl l id args t . CoreFunBody lb $ concatMap (elimUnreachableStmt . optimizeStmt) stmts

optimizeStmt :: CoreStmt -> [CoreStmt]
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
optimizeStmt (VarDeclStmt o v) = [VarDeclStmt o $ optimizeVarDecl v]
optimizeStmt (AssignStmt l i fd t e) = [AssignStmt l i fd t (optimizeExpr e)]
optimizeStmt (FunCallStmt f) = [FunCallStmt (optimizeFunCall f)]
optimizeStmt (ReturnStmt l e) = [ReturnStmt l (optimizeExpr <$> e)]

elimUnreachableStmt :: [CoreStmt] -> [CoreStmt]
elimUnreachableStmt xs =
    case L.findIndex isReturn xs of
        (Just retIx) -> L.take (retIx + 1) xs
        Nothing -> xs
    where
        isReturn (ReturnStmt _ _) = True
        isReturn _ = False

optimizeExpr :: CoreExpr -> CoreExpr
optimizeExpr e@(Op2Expr l e1 t1 op e2 t2) =
    case (optimizeExpr e1, optimizeExpr e2, op) of
        (IntExpr _ i1, IntExpr _ i2, _) -> evaluateI l i1 op i2
        (CharExpr _ b1, CharExpr _ b2, _) -> evaluateC l b1 op b2
        (BoolExpr _ c1, BoolExpr _ c2, _) -> evaluateB l c1 op c2
        (eb@(BoolExpr _ True), _, LogOr) -> eb
        (eb@(BoolExpr _ False), _, LogAnd) -> eb
        (VarIdentifierExpr f1, VarIdentifierExpr f2, Equal) | f1 == f2 -> BoolExpr l True
        (VarIdentifierExpr f1, VarIdentifierExpr f2, Nequal) | f1 == f2 -> BoolExpr l False
        (e1', e2', _) -> Op2Expr l e1' t1 op e2' t2

optimizeExpr (OpExpr l op1 e) =
    case (optimizeExpr e, op1) of
        (IntExpr _ i, UnMinus) -> IntExpr l (-i)
        (BoolExpr _ i, UnNeg) -> BoolExpr l (not i)
        (e', _) -> OpExpr l op1 e'

optimizeExpr (TupExpr l e1 e2) = TupExpr l (optimizeExpr e1) (optimizeExpr e2)
optimizeExpr (FunCallExpr f) = FunCallExpr (optimizeFunCall f)
optimizeExpr e = e

optimizeFunCall :: CoreFunCall -> CoreFunCall
optimizeFunCall (CoreFunCall l name t args) = CoreFunCall l name t (map optimizeExpr args)

evaluateI :: EntityLoc -> Integer -> OpBin -> Integer -> CoreExpr
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

evaluateC :: EntityLoc -> Char -> OpBin -> Char -> CoreExpr
evaluateC l c1 op c2 =
        case op of
            Equal -> BoolExpr l (c1 == c2)
            Less -> BoolExpr l (c1 < c2)
            Greater -> BoolExpr l (c1 > c2)
            LessEq -> BoolExpr l (c1 <= c2)
            GreaterEq -> BoolExpr l (c1 >= c2)
            Nequal -> BoolExpr l (c1 /= c2)
            _ -> error "internal optimization error: pattern should not occur"

evaluateB :: EntityLoc -> Bool -> OpBin -> Bool -> CoreExpr
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
