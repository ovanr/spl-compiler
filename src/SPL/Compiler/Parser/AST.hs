
module SPL.Compiler.Parser.AST 
    (
        ASTType(..),
        toASTType
    ) where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), Keyword(..), Type(..))
import Data.Text (Text)
import qualified Data.Text as T

-- Location is (LineNum, ColumnNum)
type Location = (Int, Int)

-- EntityLoc is StartLocation and EndLocation in source file
data EntityLoc = EntityLoc Location Location

data AST = 
      ASTNil
    | ASTCons ASTLeaf AST

data ASTLeaf = 
        ASTLeft ASTVarDecl
    |   ASTRight ASTFunDecl

data ASTFunDecl = ASTFunDecl ASTIdentifer [ASTIdentifer] ASTType ASTFunBody

data ASTVarDecl = ASTVarDecl ASTType ASTIdentifer ASTExpr

data ASTIdentifer = ASTIdentifer EntityLoc Text 

data ASTFunBody = ASTFunBody [ASTVarDecl] [ASTStmt]

data ASTFunCall = ASTFunCall EntityLoc ASTIdentifer [ASTExpr]

data ASTStmt = 
        If EntityLoc ASTExpr [ASTStmt] [ASTStmt]
    |   While EntityLoc ASTExpr [ASTStmt]
    |   Assign EntityLoc ASTIdentifer ASTExpr
    |   StmtFunCall ASTFunCall
    |   Return EntityLoc (Maybe ASTExpr)  

data ASTExpr = 
        IdentifierExpr ASTIdentifer
    |   IntExpr EntityLoc Int
    |   CharExpr EntityLoc Char
    |   BoolExpr EntityLoc Bool
    |   ExprFunCall ASTFunCall
    |   OpExpr EntityLoc ASTOpUnary ASTExpr  
    |   Op2Expr EntityLoc ASTExpr ASTOpBin ASTExpr  
    |   EmptyListExpr EntityLoc
    |   TupExpr EntityLoc ASTExpr ASTExpr

data ASTOpUnary = UnNeg | UnMinus
data ASTOpBin = 
      Plus 
    | Minus 
    | Mul 
    | Div 
    | Mod 
    | Equal 
    | Less 
    | Greater 
    | LessEq 
    | GreaterEq 
    | Nequal 
    | LogAnd 
    | LogOr 
    | Cons 

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
