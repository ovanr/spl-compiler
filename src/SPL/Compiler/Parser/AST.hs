{-# LANGUAGE TemplateHaskell #-}
module SPL.Compiler.Parser.AST where

import SPL.Compiler.Lexer.AlexLexGen (AlexPosn(..), Token(..), SPLToken(..), Keyword(..), Type(..))
import SPL.Compiler.Common.EntityLocation
import Data.Text (Text)
import Data.Graph (SCC(..))
import qualified Data.Text as T
import Control.Lens

data AST = 
    ASTUnordered [Either ASTVarDecl ASTFunDecl]
    | ASTOrdered [ASTVarDecl] [SCC ASTFunDecl]

data ASTFunDecl = 
    ASTFunDecl {
        _funLoc :: EntityLoc,
        _funId :: ASTIdentifier,
        _funArgs :: [ASTIdentifier],
        _funType :: ASTType,
        _funBody :: ASTFunBody
    }
    deriving (Eq, Show)

data ASTVarDecl = ASTVarDecl EntityLoc ASTType ASTIdentifier ASTExpr
    deriving (Eq, Show)

data ASTIdentifier = ASTIdentifier { _idLoc :: EntityLoc, _idName :: Text }
    deriving (Eq, Show)

data ASTFunBody = ASTFunBody EntityLoc [ASTVarDecl] [ASTStmt]
    deriving (Eq, Show)

data ASTFunCall = ASTFunCall EntityLoc ASTExpr [ASTExpr]
    deriving (Eq, Show)

data Field = Hd EntityLoc | Tl EntityLoc | Fst EntityLoc | Snd EntityLoc 

instance Eq Field where
    (Hd _) == (Hd _) = True
    (Tl _) == (Tl _) = True
    (Fst _) == (Fst _) = True
    (Snd _) == (Snd _) = True
    _ == _ = False

instance Show Field where
    show (Hd _) = "hd"
    show (Tl _) = "tl"
    show (Fst _) = "fst"
    show (Snd _) = "snd"

data ASTStmt = 
        IfElseStmt EntityLoc ASTExpr [ASTStmt] [ASTStmt]
    |   WhileStmt EntityLoc ASTExpr [ASTStmt]
    |   AssignStmt EntityLoc ASTIdentifier [Field] ASTExpr
    |   FunCallStmt ASTFunCall
    |   ReturnStmt EntityLoc (Maybe ASTExpr)  
    deriving (Eq, Show)

data ASTExpr = 
        IntExpr EntityLoc Integer
    |   CharExpr EntityLoc Char
    |   BoolExpr EntityLoc Bool
    |   FunCallExpr ASTFunCall
    |   IdentifierExpr ASTIdentifier
    |   FieldSelectExpr EntityLoc ASTExpr [Field]
    |   OpExpr EntityLoc OpUnary ASTExpr
    |   Op2Expr EntityLoc ASTExpr OpBin ASTExpr  
    |   EmptyListExpr EntityLoc
    |   EmptyCharListExpr EntityLoc
    |   TupExpr EntityLoc ASTExpr ASTExpr
    deriving (Eq, Show)

data OpUnary = UnNeg | UnMinus
    deriving (Eq, Show)

data OpBin = 
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
    |   ASTFunType EntityLoc [ASTType] ASTType
    |   ASTTupleType EntityLoc ASTType ASTType
    |   ASTListType EntityLoc ASTType
    |   ASTVarType EntityLoc T.Text
    |   ASTIntType EntityLoc 
    |   ASTBoolType EntityLoc 
    |   ASTCharType EntityLoc 
    |   ASTVoidType EntityLoc 
    deriving (Eq, Show)

makeLenses ''ASTFunDecl
makeLenses ''ASTIdentifier
