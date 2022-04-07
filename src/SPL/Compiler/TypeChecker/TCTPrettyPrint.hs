{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.TypeChecker.TCTPrettyPrint where
import SPL.Compiler.TypeChecker.TCT
    (TCTType(..),
     OpBin(..),
     OpUnary(..),
     TCTExpr(..),
     TCTStmt(..),
     TCTFunCall(..),
     TCTFieldSelector(..),
     TCTField(..),
     TCTFunBody(..),
     TCTIdentifier(..),
     TCTVarDecl(..),
     TCTFunDecl(..),
     TCTLeaf(..),
     TCT(..))
import Data.List (intercalate)
import Data.Text (Text)
import qualified Data.Text as T
import Test.Framework.Pretty (Pretty)

mkIdent :: Int -> Text
mkIdent n = foldl (<>) "" $ replicate n "   "

class PrettyPrint a where
    toCode :: Int -> a -> Text

instance PrettyPrint TCT where
    toCode _ (TCT leaves) = T.unlines $ map (toCode 0) leaves

instance PrettyPrint TCTLeaf where
    toCode _ (TCTVar vd) = toCode 0 vd
    toCode _ (TCTFun fd) = toCode 0 fd

instance PrettyPrint TCTVarDecl where
    toCode n (TCTVarDecl _ t id expr) = 
        mkIdent n <> toCode n t <> " " <> toCode n id <> " = " <> toCode n expr <> ";"

instance PrettyPrint TCTFunDecl where
    toCode n (TCTFunDecl _ id args t body) =
        toCode n id <> " (" <> T.intercalate "," (map (toCode n) args) <> ") ::"
                    <> toCodeFunType n t <> " " <> toCode (n + 1) body

instance PrettyPrint TCTField where
    toCode _ (Hd _) = "hd"
    toCode _ (Tl _) = "tl"
    toCode _ (Fst _) = "fst"
    toCode _ (Snd _) = "snd"

instance PrettyPrint TCTFieldSelector where
    toCode n (TCTFieldSelector _ id fs) = toCode n id <> foldMap ((<>) "." .toCode n) fs

instance PrettyPrint TCTExpr where
    toCode n (FieldSelectExpr f) = toCode n f
    toCode _ (IntExpr _ i) = T.pack $ show i
    toCode _ (CharExpr _ c) = T.pack $ show c
    toCode _ (BoolExpr _ b) = T.pack $ show b
    toCode n (FunCallExpr fCall) = toCode n fCall
    toCode n (OpExpr _ op expr) = "(" <> toCode n op <> toCode n expr <> ")"
    toCode n (Op2Expr _ lExpr op rExpr) = "(" <> toCode n lExpr <> toCode n op <> toCode n rExpr <> ")"
    toCode _ (EmptyListExpr _) = "[]"
    toCode n (TupExpr _ lVal rVal) = "(" <> toCode n lVal <> "," <> toCode n rVal <> ")"

instance PrettyPrint TCTStmt where
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
    toCode n (AssignStmt _ id expr) = mkIdent n <> toCode n id <> " = " <> toCode n expr <> ";"
    toCode n (FunCallStmt _ fCall) = mkIdent n <> toCode n fCall <> ";"
    toCode n (ReturnStmt _ Nothing) = mkIdent n <> "return;"
    toCode n (ReturnStmt _ (Just expr)) = mkIdent n <> "return " <> toCode n expr <> ";"

instance PrettyPrint TCTFunCall where
    toCode n (TCTFunCall _ id args) = toCode n id <> "(" <> T.intercalate "," (map (toCode n) args) <> ")"

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

instance PrettyPrint TCTFunBody where
    toCode n (TCTFunBody _ vars stmts) = 
        "{" <> 
            T.unlines ("": map (toCode n) vars) <> 
            T.unlines (map (toCode n) stmts) <> 
        "}"

instance PrettyPrint TCTType where
    toCode n (TCTTupleType _ lType rType) = "(" <> toCode n lType <> "," <> toCode n rType <> ")"
    toCode n (TCTListType _ t) = "[" <> toCode n t <> "]"
    toCode n (TCTVarType _ id) = id
    toCode n (TCTIntType _) = "Int"
    toCode n (TCTBoolType _) = "Bool"
    toCode n (TCTCharType _) = "Char"
    toCode n (TCTVoidType _) = "Void"
    toCode n (TCTFunType _ _ _ _) = error "Do not print TCTFunTypes using this function!"

toCodeFunType :: Int -> TCTType -> Text
toCodeFunType n (TCTFunType _ constraints t ts) = toCode n t <> " " <> toCodeFunType n ts
toCodeFunType n t = "-> " <> toCode n t

instance PrettyPrint TCTIdentifier where
    toCode n (TCTIdentifier _ id) = id
