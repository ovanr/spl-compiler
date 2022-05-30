{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
module SPL.Compiler.Parser.ASTPrettyPrint where
import SPL.Compiler.Parser.AST
    (ASTType(..),
     OpBin(..),
     OpUnary(..),
     ASTExpr(..),
     ASTStmt(..),
     ASTFunCall(..),
     Field(..),
     ASTFunBody(..),
     ASTIdentifier(..),
     ASTVarDecl(..),
     ASTFunDecl(..),
     AST(..))
import Data.List (intercalate)
import Data.Text (Text)
import Data.Graph
import qualified Data.Text as T

mkIdent :: Int -> Text
mkIdent n = foldl (<>) "" $ replicate n "   "

class PrettyPrint a where
    toCode :: Int -> a -> Text

instance PrettyPrint AST where
    toCode _ (ASTUnordered leaves) = T.unlines $ map (toCode 0) leaves
    toCode _ (ASTOrdered varDecls funDecls) = 
        T.unlines $ 
            map (toCode 0) varDecls <>
            map (toCode 0) (concatMap sccToList funDecls)

        where
            sccToList (AcyclicSCC x) = [x]
            sccToList (CyclicSCC xs) = xs

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
    toCode n (Left a) = toCode n a
    toCode n (Right b) = toCode n b

instance PrettyPrint ASTVarDecl where
    toCode n (ASTVarDecl _ (ASTUnknownType _) id expr) =
        mkIdent n <> "var " <> toCode n id <> " = " <> toCode n expr <> ";"
    toCode n (ASTVarDecl _ t id expr) = 
        mkIdent n <> toCode n t <> " " <> toCode n id <> " = " <> toCode n expr <> ";"

instance PrettyPrint ASTFunDecl where
    toCode n (ASTFunDecl _ id args t body) =
        toCode n id <> 
            " (" <> T.intercalate "," (map (toCode n) args) <> ")" <> 
            dbColon t <> toCode n t <> " " <> 
            toCode (n + 1) body
        where
            dbColon ASTUnknownType{} = ""
            dbColon _ = " :: "

instance PrettyPrint Field where
    toCode _ = T.pack . show

instance PrettyPrint ASTExpr where
    toCode n (FieldSelectExpr l e []) = toCode n e 
    toCode n (FieldSelectExpr l e fds) = "(" <> toCode n e <> ")." <> T.intercalate "." (map (toCode n) fds)
    toCode _ (IdentifierExpr i) = toCode 0 i
    toCode _ (IntExpr _ i) = T.pack $ show i
    toCode _ (CharExpr _ c) = T.pack $ show c
    toCode _ (BoolExpr _ b) = T.pack $ show b
    toCode n (FunCallExpr fCall) = toCode n fCall
    toCode n (OpExpr _ op expr) = "(" <> toCode n op <> toCode n expr <> ")"
    toCode n (Op2Expr _ lExpr op rExpr) = "(" <> toCode n lExpr <> toCode n op <> toCode n rExpr <> ")"
    toCode _ (EmptyListExpr _) = "[]"
    toCode n (TupExpr _ lVal rVal) = "(" <> toCode n lVal <> "," <> toCode n rVal <> ")"

instance PrettyPrint ASTStmt where
    toCode n (IfElseStmt _ cond thenBody elseBody) =
        mkIdent n <> "if (" <> toCode n cond <> ") {" <> 
            T.unlines ("": map (toCode (n+1)) thenBody) <> 
        mkIdent n <> "} " <>
        case elseBody of
            [] -> ""
            _ -> "else {" <> T.unlines ("": map (toCode (n+1)) elseBody) <> mkIdent n <> "}"
    toCode n (WhileStmt _ cond body) = 
        mkIdent n <> "while (" <> toCode n cond <> ") {" <> 
            T.unlines ("": map (toCode (n+1)) body) <> 
        mkIdent n <> "}"
    toCode n (AssignStmt _ id fds expr) = 
        mkIdent n <> toCode n id <> T.intercalate "." (map (toCode n) fds) <> " = " <> toCode n expr <> ";"
    toCode n (FunCallStmt fCall) = mkIdent n <> toCode n fCall <> ";"
    toCode n (ReturnStmt _ Nothing) = mkIdent n <> "return;"
    toCode n (ReturnStmt _ (Just expr)) = mkIdent n <> "return " <> toCode n expr <> ";"

instance PrettyPrint ASTFunCall where
    toCode n (ASTFunCall _ id args) = toCode n id <> "(" <> T.intercalate "," (map (toCode n) args) <> ")"

instance PrettyPrint OpUnary where
    toCode _ UnNeg = " ! "
    toCode _ UnMinus = " -"

instance PrettyPrint OpBin where
    toCode _ Plus = " + "
    toCode _ Minus = " - "
    toCode _ Mul = " * "
    toCode _ Div = " / "
    toCode _ Mod = " % "
    toCode _ Pow = " ˆ "
    toCode _ Equal = " == "
    toCode _ Less = " < "
    toCode _ Greater = " > "
    toCode _ LessEq = " <= "
    toCode _ GreaterEq = " >= "
    toCode _ Nequal = " != "
    toCode _ LogAnd = " && "
    toCode _ LogOr = " || "
    toCode _ Cons = " : "

instance PrettyPrint ASTFunBody where
    toCode n (ASTFunBody _ varDecls stmts) = 
        "{" <> 
            T.unlines ("": map (toCode n) varDecls) <> 
            T.unlines (map (toCode n) stmts) <> 
        "}"

instance PrettyPrint ASTType where
    toCode n (ASTUnknownType _) = ""
    toCode n (ASTFunType _ [] r) = "-> " <> toCode n r
    toCode n (ASTFunType _ xs r) = 
        T.intercalate " " (map argPrinter xs) <> " -> " <> toCode n r
        where
            argPrinter arg@ASTFunType{} = "(" <> toCode n arg <> ")"
            argPrinter arg = toCode n arg

    toCode n (ASTTupleType _ lType rType) = "(" <> toCode n lType <> ", " <> toCode n rType <> ")"
    toCode n (ASTListType _ t) = "[" <> toCode n t <> "]"
    toCode n (ASTVarType _ id) = id
    toCode n (ASTIntType _) = "Int"
    toCode n (ASTBoolType _) = "Bool"
    toCode n (ASTCharType _) = "Char"
    toCode n (ASTVoidType _) = "Void"

instance PrettyPrint ASTIdentifier where
    toCode n (ASTIdentifier _ id) = id
