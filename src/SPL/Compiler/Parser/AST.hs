
module SPL.Compiler.Parser.AST 
    (
        ASTType(..),
        toASTType
    ) where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), Keyword(..), Type(..))
import qualified Data.Text as T

data ASTType =
        ASTFunType [ASTType]
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
