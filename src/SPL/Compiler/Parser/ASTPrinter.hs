module SPL.Compiler.Parser.ASTPrinter where
import SPL.Compiler.Parser.AST
import Data.Tree

class TreeRepresentation a where
    toTree :: a -> Tree String

instance TreeRepresentation AST where
    toTree (AST leaves) = Node "program" (map toTree leaves)

instance TreeRepresentation ASTLeaf where
    toTree (ASTVar vd) = toTree vd
    toTree (ASTFun fd) = toTree fd

instance TreeRepresentation ASTVarDecl where
    toTree (ASTVarDecl _ t (ASTIdentifier _ id) expr) = Node "=" [Node (show t ++ " " ++ show id) [], toTree expr]

instance TreeRepresentation ASTFunDecl where
    toTree (ASTFunDecl _ (ASTIdentifier _ id) args t body) = undefined

instance TreeRepresentation ASTField where
    toTree (Hd _) = Node "hd" []
    toTree (Tl _) = Node "tl" []
    toTree (Fst _) = Node "fst" []
    toTree (Snd _) = Node "snd" []
instance TreeRepresentation ASTFieldSelector where
    toTree (ASTFieldSelector _ id fs) = Node (show id) $ map toTree fs

instance TreeRepresentation ASTExpr where
    toTree (FieldSelectExpr t) = toTree t
    toTree (IntExpr _ i) = Node (show i) []
    toTree (CharExpr _ c) = Node (show c) []
    toTree (BoolExpr _ b) = Node (show b) []
    toTree (FunCallExpr fCall) = toTree fCall
    toTree (OpExpr _ op expr) = Node (show op) [toTree expr]
    toTree (Op2Expr _ lExpr op rExpr) = Node (show op) [toTree lExpr, toTree rExpr]
    toTree (EmptyListExpr _) = Node "[]" []
    toTree (TupExpr _ lVal rVal) = Node "(_,_)" [toTree lVal, toTree rVal]

instance TreeRepresentation ASTStmt where
    toTree (IfElseStmt _ cond thenBody elseBody) = Node "if" [toTree cond, Node "then" (map toTree thenBody), Node "else" (map toTree elseBody)]
    toTree (WhileStmt _ cond body) = Node "while" [toTree cond, Node "do" (map toTree body)]
    toTree (AssignStmt _ f expr) = Node "=" [toTree f, toTree expr]
    toTree (FunCallStmt _ fCall) = toTree fCall
    toTree (ReturnStmt _ Nothing) = Node "return" []
    toTree (ReturnStmt _ (Just expr)) = Node "return" [toTree expr]

instance TreeRepresentation ASTFunCall where
    toTree (ASTFunCall _ (ASTIdentifier _ id) args) = Node "call" [Node (show id) [], Node "args" (map toTree args)]
