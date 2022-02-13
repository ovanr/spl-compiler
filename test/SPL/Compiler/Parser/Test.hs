{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE FlexibleContexts #-}

module SPL.Compiler.Parser.Test (htf_thisModulesTests) where

import Test.Framework
import SPL.Compiler.Lexer.AlexLexGen (Token(..), Type(..), Keyword(..))
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..), pType, pFargs, pFunType)
import SPL.Compiler.Parser.AST (ASTType(..))
import qualified Data.ByteString.Lazy as B
import Data.Text (Text)
import Control.Monad (forM_)
import Control.Applicative ((<|>))

executeMultipleTests :: (Eq b, Show b) => Parser Token Text b -> [([Token], Maybe b)] -> IO ()
executeMultipleTests parser tests = 
    forM_ tests $ \(input, expected) -> do
        let actual = runParser parser (ParserState 0 input)
        case expected of
            Just value -> assertEqual actual [Right (value, ParserState (length input) [])]
            _ -> mapM_ (\e -> print e >> assertLeft e) (runParser parser (ParserState 0 input))

-- Shorthand operator to create an (input, expected output) pair
infixl 1 -->
(-->) :: a -> b -> (a, Maybe b) 
input --> expected = (input, Just expected)

failure :: a -> (a, Maybe b) 
failure input = (input, Nothing)

test_parse_type = do
    let tests = [
            [TypeToken IntType] --> ASTIntType,
            [TypeToken BoolType] --> ASTBoolType,
            [TypeToken CharType] --> ASTCharType,
            [IdentifierToken "a"] --> ASTVarType "a",
            [SymbolToken '(', IdentifierToken "b", SymbolToken ',', TypeToken IntType, SymbolToken ')'] 
                --> ASTTupleType (ASTVarType "b") ASTIntType,
            [SymbolToken '[', IdentifierToken "b", SymbolToken ']'] --> ASTListType (ASTVarType "b"),
            failure [SymbolToken '[', IdentifierToken "b", TypeToken IntType, SymbolToken ']'],
            failure [SymbolToken '(', IdentifierToken "b", TypeToken IntType, SymbolToken ')']
            ]
    executeMultipleTests pType tests

test_parse_fargs = do
    let tests = [
            [IdentifierToken "a", SymbolToken ',', IdentifierToken "b"] 
                --> [IdentifierToken "a", IdentifierToken "b"],
            [IdentifierToken "a"] --> [IdentifierToken "a"],
            failure [IdentifierToken "a", SymbolToken ','],
            failure [KeywordToken Var]
            ]
    executeMultipleTests pFargs tests

test_parse_ftype = do
    let tests = [
            [SymbolToken ':', SymbolToken ':', SymbolToken '-', SymbolToken '>', TypeToken IntType]
                --> ASTFunType [ASTIntType],
            [SymbolToken ':', SymbolToken ':', TypeToken IntType, IdentifierToken "a", SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTVarType "a", ASTCharType],
            [SymbolToken ':', SymbolToken ':', TypeToken IntType, IdentifierToken "a", SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTVarType "a", ASTCharType],
            [SymbolToken ':', SymbolToken ':', TypeToken IntType, SymbolToken '[', IdentifierToken "a", SymbolToken ']', SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTListType (ASTVarType "a"), ASTCharType],
            failure [SymbolToken ':', SymbolToken ':', SymbolToken '-', SymbolToken '>', SymbolToken '{'],
            failure [SymbolToken ':', SymbolToken ':', TypeToken CharType]
            ]
    executeMultipleTests pFunType tests
