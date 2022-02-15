{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE FlexibleContexts #-}

module SPL.Compiler.Parser.Test (htf_thisModulesTests) where

import Test.Framework
import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..), Type(..), Keyword(..))
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

mkToken :: SPLToken -> Token
mkToken = MkToken (AlexPn 0 1 1)

failure :: a -> (a, Maybe b) 
failure input = (input, Nothing)

-- data AlexPosn = AlexPn !Int !Int !Int

test_parse_type = do
    let tests = [
            [mkToken $ TypeToken IntType] --> ASTIntType,
            [mkToken $ TypeToken BoolType] --> ASTBoolType,
            [mkToken $ TypeToken CharType] --> ASTCharType,
            [mkToken $ IdentifierToken "a"] --> ASTVarType "a",
            map mkToken [ SymbolToken '(', IdentifierToken "b", SymbolToken ',', TypeToken IntType, SymbolToken ')'] 
                --> ASTTupleType (ASTVarType "b") ASTIntType,
            map mkToken [SymbolToken '[', IdentifierToken "b", SymbolToken ']'] --> ASTListType (ASTVarType "b"),
            failure . map mkToken $ [SymbolToken '[', IdentifierToken "b", TypeToken IntType, SymbolToken ']'],
            failure . map mkToken $ [SymbolToken '(', IdentifierToken "b", TypeToken IntType, SymbolToken ')']
            ]
    executeMultipleTests pType tests

test_parse_fargs = do
    let tests = [
            map mkToken [IdentifierToken "a", SymbolToken ',', IdentifierToken "b"] 
                --> map mkToken [IdentifierToken "a", IdentifierToken "b"],
            map mkToken [IdentifierToken "a"] --> map mkToken [IdentifierToken "a"],
            failure . map mkToken $ [IdentifierToken "a", SymbolToken ','],
            failure . map mkToken $ [KeywordToken Var]
            ]
    executeMultipleTests pFargs tests

test_parse_ftype = do
    let tests = [
            map mkToken [SymbolToken ':', SymbolToken ':', SymbolToken '-', SymbolToken '>', TypeToken IntType]
                --> ASTFunType [ASTIntType],
            map mkToken [SymbolToken ':', SymbolToken ':', TypeToken IntType, IdentifierToken "a", SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTVarType "a", ASTCharType],
            map mkToken [SymbolToken ':', SymbolToken ':', TypeToken IntType, IdentifierToken "a", SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTVarType "a", ASTCharType],
            map mkToken [SymbolToken ':', SymbolToken ':', TypeToken IntType, SymbolToken '[', IdentifierToken "a", SymbolToken ']', SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTListType (ASTVarType "a"), ASTCharType],
            failure . map mkToken $ [SymbolToken ':', SymbolToken ':', SymbolToken '-', SymbolToken '>', SymbolToken '{'],
            failure . map mkToken $ [SymbolToken ':', SymbolToken ':', TypeToken CharType]
            ]
    executeMultipleTests pFunType tests
