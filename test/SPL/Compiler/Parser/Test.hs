{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE FlexibleContexts #-}

module SPL.Compiler.Parser.Test (htf_thisModulesTests) where

import Test.Framework
import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..), Type(..), Keyword(..))
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..), pType, pFargs, pFunType)
import SPL.Compiler.Parser.AST
import qualified Data.ByteString.Lazy as B
import Data.Text (Text)
import Control.Monad (forM_)
import Control.Applicative ((<|>))
import Control.Lens ((^..), (^?), _Right, ix, _1)

executeMultipleTests :: (Eq b, Show b) => Parser Token Text b -> [([SPLToken], Maybe b)] -> IO ()
executeMultipleTests parser tests = 
    forM_ tests $ \(input, expected) -> do
        let tokens = map mkToken input
        let actual = runParser parser (ParserState 0 tokens)
        case expected of
            Just value -> do
                let a = actual ^? ix 0. _Right. _1
                assertEqual (Just value) a
            _ -> mapM_ (\e -> print e >> assertLeft e) (runParser parser (ParserState 0 tokens))

-- Shorthand operator to create an (input, expected output) pair
infixl 1 -->
(-->) :: a -> b -> (a, Maybe b) 
input --> expected = (input, Just expected)

-- data AlexPosn = AlexPn !Int !Int !Int

mkToken :: SPLToken -> Token
mkToken = MkToken (AlexPn 0 1 1)

failure :: a -> (a, Maybe b) 
failure input = (input, Nothing)


test_parse_type = do
    let tests = [
            [TypeToken IntType] --> ASTIntType,
            [TypeToken BoolType] --> ASTBoolType,
            [TypeToken CharType] --> ASTCharType,
            [IdentifierToken "a"] --> ASTVarType "a",
            [ SymbolToken '(', IdentifierToken "b", SymbolToken ',', TypeToken IntType, SymbolToken ')'] 
                --> ASTTupleType (ASTVarType "b") ASTIntType,
            [SymbolToken '[', IdentifierToken "b", SymbolToken ']'] --> ASTListType (ASTVarType "b"),
            failure [SymbolToken '[', IdentifierToken "b", TypeToken IntType, SymbolToken ']'],
            failure [SymbolToken '(', IdentifierToken "b", TypeToken IntType, SymbolToken ')']
            ]
    executeMultipleTests pType tests

test_parse_fargs = do
    let tests = [
            [IdentifierToken "a", SymbolToken ',', IdentifierToken "b"] 
                --> [ASTIdentifier (EntityLoc (1,1) (1,1)) "a", ASTIdentifier (EntityLoc (1,1) (1,1)) "b"],
            [IdentifierToken "a"] --> [ASTIdentifier (EntityLoc (1,1) (1,1)) "a"],
            [] --> [],
            [IdentifierToken "a", SymbolToken ','] --> [],
            [KeywordToken Var] --> []
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
