module SPL.Compiler.TypeChecker.TCT where

import SPL.Compiler.Lexer.AlexLexGen (AlexPosn(..), Token(..), SPLToken(..), Keyword(..), Type(..))
import SPL.Compiler.Common.EntityLocation (EntityLoc(..))
import SPL.Compiler.Parser.AST (OpUnary(..), OpBin(..))
import Data.Text (Text)
import Data.Set (Set)
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

data TCTVarDecl = TCTVarDecl EntityLoc TCTType TCTIdentifier TCTExpr
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
    |   OpExpr EntityLoc OpUnary TCTExpr
    |   Op2Expr EntityLoc TCTExpr OpBin TCTExpr  
    |   EmptyListExpr EntityLoc
    |   TupExpr EntityLoc TCTExpr TCTExpr
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
    |   TCTUniversalType EntityLoc (Set TypeVar) TCTType
    |   TCTTupleType EntityLoc TCTType TCTType
    |   TCTListType EntityLoc TCTType
    |   TCTFunType EntityLoc [TypeConstraints] TCTType TCTType
    deriving (Eq)

instance Show TCTType where
    show (TCTIntType _) = "Int"
    show (TCTBoolType _) = "Bool"
    show (TCTCharType _) = "Char"
    show (TCTVoidType _) = "Void"
    show (TCTVarType _ a) = T.unpack a
    show (TCTUniversalType _ _ a) = show a
    show (TCTListType _ a) = "[" <> show a <> "]"
    show (TCTTupleType _ a b) = "(" <> show a <> "," <> show b <> ")"
    show (TCTFunType _ _ a b) =
        case a of
            TCTFunType {} -> "(" <> show a <> ")" <> " -> " <> show b
            _ -> show a <> " -> " <> show b
