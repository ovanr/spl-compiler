{-# LANGUAGE TemplateHaskell #-}

module SPL.Compiler.Parser.AST where

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

data AST = 
      ASTNil
    | ASTCons ASTLeaf AST

data ASTLeaf = 
        ASTLeft ASTVarDecl
    |   ASTRight ASTFunDecl

data ASTFunDecl = ASTFunDecl ASTIdentifier [ASTIdentifier] ASTType ASTFunBody
    deriving (Eq, Show)

data ASTVarDecl = ASTVarDecl ASTType ASTIdentifier ASTExpr
    deriving (Eq, Show)

data ASTIdentifier = ASTIdentifier EntityLoc Text 
    deriving (Eq, Show)

data ASTFunBody = ASTFunBody [ASTVarDecl] [ASTStmt]
    deriving (Eq, Show)

data ASTFunCall = ASTFunCall EntityLoc ASTIdentifier [ASTExpr]
    deriving (Eq, Show)

data ASTStmt = 
        IfElse EntityLoc ASTExpr [ASTStmt] [ASTStmt]
    |   While EntityLoc ASTExpr [ASTStmt]
    |   Assign EntityLoc ASTIdentifier ASTExpr
    |   FunCallStmt ASTFunCall
    |   Return EntityLoc (Maybe ASTExpr)  
    deriving (Eq, Show)

data ASTExpr = 
        IdentifierExpr ASTIdentifier
    |   IntExpr EntityLoc Integer
    |   CharExpr EntityLoc Char
    |   BoolExpr EntityLoc Bool
    |   FunCallExpr ASTFunCall
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
        ASTUnknownType
    |   ASTFunType [ASTType]
    |   ASTTupleType ASTType ASTType
    |   ASTListType ASTType
    |   ASTVarType T.Text
    |   ASTIntType
    |   ASTBoolType
    |   ASTCharType
    |   ASTVoidType
    deriving (Eq, Show)

toASTType :: Type -> ASTType
toASTType VoidType = ASTVoidType
toASTType IntType = ASTIntType
toASTType BoolType = ASTBoolType
toASTType CharType = ASTCharType
