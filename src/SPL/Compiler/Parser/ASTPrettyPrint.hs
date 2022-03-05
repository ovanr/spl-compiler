module SPL.Compiler.Parser.ASTPrettyPrint where
import SPL.Compiler.Parser.AST
import Data.List
import Test.Framework.Pretty (Pretty)

import Data.Text (unpack)

class PrettyPrint a where
    toCode :: a -> String

instance PrettyPrint AST where
    toCode (AST leaves) = unwords $ map toCode leaves

instance PrettyPrint ASTLeaf where
    toCode (ASTVar vd) = toCode vd
    toCode (ASTFun fd) = toCode fd

instance PrettyPrint ASTVarDecl where
    toCode (ASTVarDecl _ (ASTUnknownType _) id expr) = "var " ++ toCode id ++ " = " ++ toCode expr ++ ";"
    toCode (ASTVarDecl _ t id expr) = toCode t ++ " " ++ toCode id ++ " = " ++ toCode expr ++ ";"

instance PrettyPrint ASTFunDecl where
    toCode (ASTFunDecl _ id args t body) = toCode id ++ "(" ++ intercalate "," (map toCode args) ++ ")" ++ toCode t ++ toCode body

instance PrettyPrint ASTExpr where
    toCode (IdentifierExpr id) = toCode id
    toCode (IntExpr _ i) = show i
    toCode (CharExpr _ c) = "'" ++ show c ++ "'"
    toCode (BoolExpr _ b) = show b
    toCode (FunCallExpr fCall) = toCode fCall
    toCode (OpExpr _ op expr) = "(" ++ toCode op ++ toCode expr ++ ")"
    toCode (Op2Expr _ lExpr op rExpr) = "(" ++ toCode lExpr ++ toCode op ++ toCode rExpr ++ ")"
    toCode (EmptyListExpr _) = "[]"
    toCode (TupExpr _ lVal rVal) = "(" ++ toCode lVal ++ "," ++ toCode rVal ++ ")"

instance PrettyPrint ASTStmt where
    toCode (IfElseStmt _ cond thenBody elseBody) = "if" ++ toCode cond ++ "{" ++ unwords (map toCode thenBody) ++ "}" ++ "else" ++ "{" ++ unwords (map toCode elseBody) ++ "}"
    toCode (WhileStmt _ cond body) = "while" ++ toCode cond ++ "{" ++ unwords (map toCode body) ++ "}"
    toCode (AssignStmt _ id expr) = toCode id ++ "=" ++ toCode expr ++ ";"
    toCode (FunCallStmt _ fCall) = toCode fCall ++ ";"
    toCode (ReturnStmt _ Nothing) = "return;"
    toCode (ReturnStmt _ (Just expr)) = "return" ++ toCode expr ++ ";"

instance PrettyPrint ASTFunCall where
    toCode (ASTFunCall _ id args) = toCode id ++ "(" ++ intercalate "," (map toCode args) ++ ")"

instance PrettyPrint ASTOpUnary where
    toCode UnNeg = " ! "
    toCode UnMinus = " - "

instance PrettyPrint ASTOpBin where
    toCode Plus = " + "
    toCode Minus = " - "
    toCode Mul = " * "
    toCode Div = " / "
    toCode Mod = " % "
    toCode Pow = " ˆ "
    toCode Equal = " == "
    toCode Less = " < "
    toCode Greater = " > "
    toCode LessEq = " <= "
    toCode GreaterEq = " >= "
    toCode Nequal = " != "
    toCode LogAnd = " && "
    toCode LogOr = " || "
    toCode Cons = " : "

instance PrettyPrint ASTFunBody where 
    toCode (ASTFunBody _ vars stmts) = "{" ++ unwords (map toCode vars) ++ unwords (map toCode stmts) ++ "}"


instance PrettyPrint ASTType where
    toCode (ASTUnknownType _) = ""
    toCode (ASTFunType _ ts) = " :: " ++ toCode' ts
        where
            toCode' [t] = "-> " ++ toCode t
            toCode' (t:ts) = toCode t ++ " " ++ toCode' ts
            toCode' [] = error "empty list is not expected"
    toCode (ASTTupleType _ lType rType) = "(" ++ toCode lType ++ "," ++ toCode rType ++ ")"
    toCode (ASTListType _ t) = "[" ++ toCode t ++ "]"
    toCode (ASTVarType _ id) = show id
    toCode (ASTIntType _) = "Int"
    toCode (ASTBoolType _) = "Bool"
    toCode (ASTCharType _) = "Char"
    toCode (ASTVoidType _) = "Void"

instance PrettyPrint ASTIdentifier where
    toCode (ASTIdentifier _ id) = unpack id