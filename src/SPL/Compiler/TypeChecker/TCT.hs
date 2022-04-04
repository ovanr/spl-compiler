module SPL.Compiler.TypeChecker.TCT where

import SPL.Compiler.Lexer.AlexLexGen (AlexPosn(..), Token(..), SPLToken(..), Keyword(..), Type(..))
import SPL.Compiler.Parser.AST (EntityLoc(..))
import Data.Text (Text)
import qualified Data.Text as T
import Control.Lens

type TypeVar = Text

newtype TCT = TCT [TCTLeaf]

data TCTLeaf = 
        TCTVar TCTVarDecl
    |   TCTFun TCTFunDecl

data TCTFunDecl = 
    TCTFunDecl 
        EntityLoc 
        TCTIdentifier 
        [TCTIdentifier] 
        TCTType 
        TCTFunBody
    deriving (Eq, Show)

data TCTVarDecl = EntityLoc TCTType TCTIdentifier TCTExpr
    deriving (Eq, Show)

data TCTIdentifier = TCTIdentifier EntityLoc Text 
    deriving (Eq, Show)

data TCTFunBody = TCTFunBody EntityLoc [TCTVarDecl] [TCTStmt]
    deriving (Eq, Show)

data TCTFunCall = TCTFunCall EntityLoc TCTIdentifier [TCTExpr]
    deriving (Eq, Show)

data TCTFieldSelector = TCTFieldSelector EntityLoc TCTIdentifier [TCTField]
    deriving (Eq, Show)

data TCTField = Hd EntityLoc | Tl EntityLoc | Fst EntityLoc | Snd EntityLoc 
    deriving (Eq, Show)

data TCTStmt = 
        IfElseStmt EntityLoc TCTExpr [TCTStmt] [TCTStmt]
    |   WhileStmt EntityLoc TCTExpr [TCTStmt]
    |   AssignStmt EntityLoc TCTFieldSelector TCTExpr
    |   FunCallStmt EntityLoc TCTFunCall
    |   ReturnStmt EntityLoc (Maybe TCTExpr)  
    deriving (Eq, Show)

data TCTExpr = 
        IntExpr EntityLoc Integer
    |   CharExpr EntityLoc Char
    |   BoolExpr EntityLoc Bool
    |   FunCallExpr TCTFunCall
    |   FieldSelectExpr TCTFieldSelector
    |   OpExpr EntityLoc TCTOpUnary TCTExpr
    |   Op2Expr EntityLoc TCTExpr TCTOpBin TCTExpr  
    |   EmptyListExpr EntityLoc
    |   TupExpr EntityLoc TCTExpr TCTExpr
    deriving (Eq, Show)

data TCTOpUnary = UnNeg | UnMinus
    deriving (Eq, Show)

data TCTOpBin = 
      Plus 
    | Minus 
    | Mul 
    | Div 
    | Mod 
    | Pow
    | Equal 
    | Less 
    | Greater 
    | LessEq 
    | GreaterEq 
    | Nequal 
    | LogAnd 
    | LogOr 
    | Cons 
    deriving (Eq, Show)

data TypeConstraints =
        Eq T.Text
    |   Ord T.Text
    |   Print T.Text
    deriving (Eq, Show)

data TCTType =
        TCTIntType EntityLoc
    |   TCTBoolType EntityLoc
    |   TCTCharType EntityLoc
    |   TCTVoidType EntityLoc
    |   TCTVarType EntityLoc TypeVar
    |   TCTTupleType EntityLoc Type Type
    |   TCTListType EntityLoc Type
    |   TCTFunType EntityLoc [TypeConstraints] Type Type
    deriving (Eq)

instance Show TCTType where
    show (TCTIntType _) = "Int"
    show (TCTBoolType _) = "Bool"
    show (TCTCharType _) = "Char"
    show (TCTVoidType _) = "Void"
    show (TCTVarType _ a) = T.unpack a
    show (TCTListType _ a) = "[" <> show a <> "]"
    show (TCTTupleType _ a b) = "(" <> show a <> "," <> show b <> ")"
    show (TCTFunType _ _ a b) =
        case a of
            TCTFunType {} -> "(" <> show a <> ")" <> " -> " <> show b
            _ -> show a <> " -> " <> show b
