{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
module SPL.Compiler.SemanticAnalysis.CorePrettyPrint where

import SPL.Compiler.SemanticAnalysis.Core
    (CoreType(..),
     OpBin(..),
     OpUnary(..),
     CoreExpr(..),
     CoreStmt(..),
     CoreFunCall(..),
     Field(..),
     CoreFunBody(..),
     CoreIdentifier(..),
     CoreVarDecl(..),
     CoreFunDecl(..),
     Core(..))
import Data.List (intercalate)
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Text as T
import Data.Graph
import Data.Either.Extra (mapLeft)

mkIdent :: Int -> Text
mkIdent n = foldl (<>) "" $ replicate n "   "

class PrettyPrint a where
    toCode :: Int -> a -> Text

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
    toCode n (Left a) = toCode n a
    toCode n (Right b) = toCode n b

instance PrettyPrint Core where
    toCode _ (Core varDecls funDecls) =
        T.unlines .
        (\xs -> if null xs then xs else init xs) .
        concatMap (\i -> [i, mempty]) $
        map (toCode 0) varDecls <> concatMap (map (toCode 0) . unSCC) funDecls
        where
            unSCC (AcyclicSCC x) = [x]
            unSCC (CyclicSCC xs) = xs

instance PrettyPrint CoreVarDecl where
    toCode n (CoreVarDecl _ t id expr) =
        mkIdent n <> toCode n t <> " " <> toCode n id <> " = " <> toCode n expr <> ";"

instance PrettyPrint CoreFunDecl where
    toCode n (CoreFunDecl _ id args t body) =
        toCode n id <> " (" <> T.intercalate "," (map (toCode n) args) <> ") :: "
                    <> toCode n t <> " " <> toCode (n + 1) body

instance PrettyPrint Field where
    toCode _ (Hd _) = "hd"
    toCode _ (Tl _) = "tl"
    toCode _ (Fst _) = "fst"
    toCode _ (Snd _) = "snd"

instance PrettyPrint CoreExpr where
    toCode _ (IntExpr _ i) = T.pack $ show i
    toCode _ (CharExpr _ c) = T.pack $ show c
    toCode _ (BoolExpr _ b) = T.pack $ show b
    toCode _ (FunIdentifierExpr _ (CoreIdentifier _ i)) = i
    toCode _ (VarIdentifierExpr (CoreIdentifier _ i)) = i
    toCode n (FunCallExpr fCall) = toCode n fCall
    toCode n (OpExpr _ op expr) = "(" <> toCode n op <> toCode n expr <> ")"
    toCode n (Op2Expr _ lExpr _ op rExpr _) = "(" <> toCode n lExpr <> toCode n op <> toCode n rExpr <> ")"
    toCode n (EmptyListExpr _ _) = "[]"
    toCode n (TupExpr _ lVal rVal) = "(" <> toCode n lVal <> "," <> toCode n rVal <> ")"

instance PrettyPrint CoreStmt where
    toCode n (IfElseStmt _ cond thenBody elseBody) =
        mkIdent n <> "if (" <> toCode n cond <> ") {" <>
            T.unlines ("": map (toCode (n+1)) thenBody) <>
        mkIdent n <> "} " <>
        case elseBody of
            [] -> ""
            _ -> "else {" <> T.unlines ("" : map (toCode (n+1)) elseBody) <> mkIdent n <> "}"
    toCode n (WhileStmt _ cond body) =
        mkIdent n <> "while (" <> toCode n cond <> ") {" <>
            T.unlines ("": map (toCode (n+1)) body) <>
        mkIdent n <> "}"
    toCode n (VarDeclStmt _ v) = toCode n v
    toCode n (AssignStmt _ id t [] expr) =
        mkIdent n <> toCode n id <> " = " <> toCode n expr <> ";"
    toCode n (AssignStmt _ id t fd expr) =
        mkIdent n <> toCode n id <> "." <>  T.intercalate "." (map (toCode n) fd) <> " = " <> toCode n expr <> ";"
    toCode n (FunCallStmt fCall) = mkIdent n <> toCode n fCall <> ";"
    toCode n (ReturnStmt _ Nothing) = mkIdent n <> "return;"
    toCode n (ReturnStmt _ (Just expr)) = mkIdent n <> "return " <> toCode n expr <> ";"

instance PrettyPrint CoreFunCall where
    toCode n (CoreFunCall _ id t args) =
        toCode n id <>
        "(" <> T.intercalate "," (map (toCode n) args) <> ")"

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

instance PrettyPrint CoreFunBody where
    toCode n (CoreFunBody _ stmts) =
        "{" <> T.unlines ("": map (toCode n) stmts) <> "}"

instance PrettyPrint CoreType where
    toCode n = T.pack . show

instance PrettyPrint CoreIdentifier where
    toCode n (CoreIdentifier _ id) = id
