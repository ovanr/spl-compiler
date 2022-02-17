
module SPL.Compiler.Parser.AST where

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

data ASTFunCall = ASTFunCall ASTIdentifer [ASTExpr]

data ASTStmt = 
        If EntityLoc ASTExpr [ASTStmt] [ASTStmt]
    |   While EntityLoc ASTExpr [ASTStmt]
    |   Assign EntityLoc ASTIdentifer ASTExpr
    |   FunCallStmt EntityLoc ASTFunCall
    |   Return EntityLoc (Maybe ASTExpr)  

data ASTExpr = 
        IdentifierExpr ASTIdentifer
    |   IntExpr EntityLoc Int
    |   CharExpr EntityLoc Char
    |   BoolExpr EntityLoc Bool
    |   FunCallExpr EntityLoc ASTFunCall
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

getStartLoc :: ASTExpr -> Location
getStartLoc (IdentifierExpr (ASTIdentifer (EntityLoc start _) _)) = start
getStartLoc (IntExpr (EntityLoc start _) _) = start
getStartLoc (CharExpr (EntityLoc start _) _) = start
getStartLoc (BoolExpr (EntityLoc start _) _) = start
getStartLoc (FunCallExpr (EntityLoc start _) _) = start
getStartLoc (OpExpr (EntityLoc start _) _ _) = start 
getStartLoc (Op2Expr (EntityLoc start _) _ _ _) = start  
getStartLoc (EmptyListExpr (EntityLoc start _)) = start
getStartLoc (TupExpr (EntityLoc start _) _ _) = start

getEndLoc :: ASTExpr -> Location
getEndLoc (IdentifierExpr (ASTIdentifer (EntityLoc _ end) _)) = end
getEndLoc (IntExpr (EntityLoc _ end) _) = end
getEndLoc (CharExpr (EntityLoc _ end) _) = end
getEndLoc (BoolExpr (EntityLoc _ end) _) = end
getEndLoc (FunCallExpr (EntityLoc _ end) _) = end
getEndLoc (OpExpr (EntityLoc _ end) _ _) = end 
getEndLoc (Op2Expr (EntityLoc _ end) _ _ _) = end  
getEndLoc (EmptyListExpr (EntityLoc _ end)) = end
getEndLoc (TupExpr (EntityLoc _ end) _ _) = end
