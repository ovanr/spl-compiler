module SPL.Compiler.Parser.AST where

import SPL.Compiler.Lexer.AlexLexGen (AlexPosn(..), Token(..), SPLToken(..), Keyword(..), Type(..))
import Data.Text (Text)
import qualified Data.Text as T

-- Location is (LineNum, ColumnNum)
type Location = (Int, Int)

-- EntityLoc is StartLocation and EndLocation in source file
data EntityLoc = EntityLoc Location Location
    deriving (Eq, Show)

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
        If EntityLoc ASTExpr [ASTStmt] [ASTStmt]
    |   While EntityLoc ASTExpr [ASTStmt]
    |   Assign EntityLoc ASTIdentifier ASTExpr
    |   FunCallStmt ASTFunCall
    |   Return EntityLoc (Maybe ASTExpr)  
    deriving (Eq, Show)

data ASTExpr = 
        IdentifierExpr ASTIdentifier
    |   IntExpr EntityLoc Int
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

getStartLoc :: ASTExpr -> Location
getStartLoc (IdentifierExpr (ASTIdentifier (EntityLoc start _) _)) = start
getStartLoc (IntExpr (EntityLoc start _) _) = start
getStartLoc (CharExpr (EntityLoc start _) _) = start
getStartLoc (BoolExpr (EntityLoc start _) _) = start
getStartLoc (FunCallExpr (ASTFunCall (EntityLoc start _) _ _)) = start
getStartLoc (OpExpr (EntityLoc start _) _ _) = start 
getStartLoc (Op2Expr (EntityLoc start _) _ _ _) = start  
getStartLoc (EmptyListExpr (EntityLoc start _)) = start
getStartLoc (TupExpr (EntityLoc start _) _ _) = start

getEndLoc :: ASTExpr -> Location
getEndLoc (IdentifierExpr (ASTIdentifier (EntityLoc _ end) _)) = end
getEndLoc (IntExpr (EntityLoc _ end) _) = end
getEndLoc (CharExpr (EntityLoc _ end) _) = end
getEndLoc (BoolExpr (EntityLoc _ end) _) = end
getEndLoc (FunCallExpr (ASTFunCall (EntityLoc _ end) _ _)) = end
getEndLoc (OpExpr (EntityLoc _ end) _ _) = end 
getEndLoc (Op2Expr (EntityLoc _ end) _ _ _) = end  
getEndLoc (EmptyListExpr (EntityLoc _ end)) = end
getEndLoc (TupExpr (EntityLoc _ end) _ _) = end

tokenToEntityLoc :: Token -> EntityLoc
tokenToEntityLoc token@(MkToken (AlexPn t l c) splToken) = EntityLoc (l,c) (l,c + lengthOfToken token)
    where
        -- TODO: Add proper implementation later
        lengthOfToken :: Token -> Int 
        lengthOfToken token = 0
tokenToEntityLoc _ = EntityLoc (0,0) (0,0)

locationRange :: EntityLoc -> EntityLoc -> EntityLoc 
locationRange (EntityLoc start _) (EntityLoc _ end) = EntityLoc start end

tokLoc :: Token -> Location
tokLoc (MkToken (AlexPn ln col _) _) = (ln,col)
tokLoc EOF = (0,0)

