{-# LANGUAGE TemplateHaskell #-}

module SPL.Compiler.TypeChecker.AST where

import SPL.Compiler.Lexer.AlexLexGen (AlexPosn(..), Token(..), SPLToken(..), Keyword(..), Type(..))
import Data.Text (Text)
import qualified Data.Text as T
import Control.Lens

-- Location is (LineNum, ColumnNum)
type Location = (Int, Int)

-- EntityLoc is StartLocation and EndLocation in source file
data EntityLoc = EntityLoc {
    _locStart :: Location,
    _locEnd :: Location
} deriving (Eq, Show)

makeLenses ''EntityLoc

newtype AST = AST [ASTLeaf]

data ASTLeaf = 
        ASTVar ASTVarDecl
    |   ASTFun ASTFunDecl

data ASTFunDecl = 
    ASTFunDecl 
        EntityLoc 
        ASTIdentifier 
        [ASTIdentifier] 
        ASTType 
        ASTFunBody
    deriving (Eq, Show)

data ASTVarDecl = ASTVarDecl EntityLoc ASTType ASTIdentifier ASTExpr
    deriving (Eq, Show)

data ASTIdentifier = ASTIdentifier EntityLoc Text 
    deriving (Eq, Show)

data ASTFunBody = ASTFunBody EntityLoc [ASTVarDecl] [ASTStmt]
    deriving (Eq, Show)

data ASTFunCall = ASTFunCall EntityLoc ASTIdentifier [ASTExpr]
    deriving (Eq, Show)

data ASTFieldSelector = ASTFieldSelector EntityLoc ASTIdentifier [ASTField]
    deriving (Eq, Show)

data ASTField = Hd EntityLoc | Tl EntityLoc | Fst EntityLoc | Snd EntityLoc 
    deriving (Eq, Show)

data ASTStmt = 
        IfElseStmt EntityLoc ASTExpr [ASTStmt] [ASTStmt]
    |   WhileStmt EntityLoc ASTExpr [ASTStmt]
    |   AssignStmt EntityLoc ASTFieldSelector ASTExpr
    |   FunCallStmt EntityLoc ASTFunCall
    |   ReturnStmt EntityLoc (Maybe ASTExpr)  
    deriving (Eq, Show)

data ASTExpr = 
        IntExpr EntityLoc Integer
    |   CharExpr EntityLoc Char
    |   BoolExpr EntityLoc Bool
    |   FunCallExpr ASTFunCall
    |   FieldSelectExpr ASTFieldSelector
    |   OpExpr EntityLoc ASTOpUnary ASTExpr  
    |   Op2Expr EntityLoc ASTExpr ASTOpBin ASTExpr  
    |   EmptyListExpr EntityLoc
    |   TupExpr EntityLoc ASTExpr ASTExpr
    deriving (Eq, Show)

data ASTOpUnary = UnNeg | UnMinus
    deriving (Eq, Show)

data ASTOpBin = 
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

data ASTType =
        ASTUnknownType EntityLoc
    |   ASTFunType EntityLoc [ASTType]
    |   ASTTupleType EntityLoc ASTType ASTType
    |   ASTListType EntityLoc ASTType
    |   ASTVarType EntityLoc T.Text
    |   ASTIntType EntityLoc 
    |   ASTBoolType EntityLoc 
    |   ASTCharType EntityLoc 
    |   ASTVoidType EntityLoc 
    deriving (Eq, Show)
