{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module SPL.Compiler.Lexer.Test (htf_thisModulesTests) where

import Test.Framework
import SPL.Compiler.Lexer.AlexLexGen (tokenize, Token(..), Keyword(..), SPLToken(..), Type(..), AlexPosn(..))
import qualified Data.ByteString.Lazy as B

tokenize_file fl = do
    contents <- B.readFile fl
    return $ tokenize fl contents
    
test_tokenize_at_sign_in_identifier = do
    actual <- tokenize_file "test/SPL/Compiler/Lexer/at_sign_in_id.spl"
    assertLeft actual

test_tokenize_multi_line_comment = do
    actual <- tokenize_file "test/SPL/Compiler/Lexer/multi_line_comment.spl"
    let expected = [MkToken (AlexPn 0 1 1) (KeywordToken While),
                    MkToken (AlexPn 8 2 2) (IdentifierToken "id23"),
                    MkToken (AlexPn 27 4 2) (IdentifierToken "how"),
                    MkToken (AlexPn 69 9 2) (IntToken 233),
                    MkToken (AlexPn 73 9 6) (IdentifierToken "okay"),
                    EOF]
    
    assertEqual actual (Right expected)

test_tokenize_characters = do
    actual <- tokenize_file "test/SPL/Compiler/Lexer/characters.spl"
    let expected = [MkToken (AlexPn 1 1 2) (IdentifierToken "in"),
                    MkToken (AlexPn 4 1 5) (CharToken 'o'),
                    MkToken (AlexPn 10 2 2) (IdentifierToken "then"),
                    MkToken (AlexPn 15 2 7) (IdentifierToken "how"),
                    MkToken (AlexPn 20 3 2) (IdentifierToken "about"),
                    MkToken (AlexPn 26 3 8) (CharToken '\\'), 
                    EOF]    

    assertEqual actual (Right expected)

test_tokenize_stress = do
    actual <- tokenize_file "test/SPL/Compiler/Lexer/stress.spl"
    let expected =
            [ MkToken (AlexPn 0 1 1) (SymbolToken '(')
            , MkToken (AlexPn 1 1 2) (SymbolToken '(')
            , MkToken (AlexPn 2 1 3) (SymbolToken '[')
            , MkToken (AlexPn 3 1 4) (SymbolToken ']')
            , MkToken (AlexPn 5 1 6) (SymbolToken ':')
            , MkToken (AlexPn 7 1 8) (SymbolToken '-')
            , MkToken (AlexPn 8 1 9) (SymbolToken '(')
            , MkToken (AlexPn 9 1 10) (IntToken 1)
            , MkToken (AlexPn 10 1 11) (SymbolToken '*')
            , MkToken (AlexPn 11 1 12) (SymbolToken '[')
            , MkToken (AlexPn 12 1 13) (SymbolToken ']')
            , MkToken (AlexPn 13 1 14) (SymbolToken ')')
            , MkToken (AlexPn 14 1 15) (SymbolToken '-')
            , MkToken (AlexPn 15 1 16) (SymbolToken '(')
            , MkToken (AlexPn 16 1 17) (IntToken 2)
            , MkToken (AlexPn 17 1 18) (SymbolToken '*')
            , MkToken (AlexPn 18 1 19) (SymbolToken '[')
            , MkToken (AlexPn 19 1 20) (SymbolToken ']')
            , MkToken (AlexPn 20 1 21) (SymbolToken '-')
            , MkToken (AlexPn 21 1 22) (IntToken 3)
            , MkToken (AlexPn 22 1 23) (SymbolToken '*')
            , MkToken (AlexPn 23 1 24) (SymbolToken '[')
            , MkToken (AlexPn 24 1 25) (SymbolToken ']')
            , MkToken (AlexPn 25 1 26) (SymbolToken ')')
            , MkToken (AlexPn 26 1 27) (SymbolToken '-')
            , MkToken (AlexPn 27 1 28) (IntToken 4)
            , MkToken (AlexPn 28 1 29) (SymbolToken '/')
            , MkToken (AlexPn 29 1 30) (SymbolToken '[')
            , MkToken (AlexPn 30 1 31) (SymbolToken ']')
            , MkToken (AlexPn 31 1 32) (SymbolToken '/')
            , MkToken (AlexPn 32 1 33) (SymbolToken '-')
            , MkToken (AlexPn 33 1 34) (IntToken 5)
            , MkToken (AlexPn 34 1 35) (SymbolToken ')')
            , MkToken (AlexPn 35 1 36) (SymbolToken ':')
            , MkToken (AlexPn 37 1 38) (SymbolToken '(')
            , MkToken (AlexPn 38 1 39) (IntToken 1)
            , MkToken (AlexPn 39 1 40) (SymbolToken '*')
            , MkToken (AlexPn 40 1 41) (SymbolToken '[')
            , MkToken (AlexPn 41 1 42) (SymbolToken ']')
            , MkToken (AlexPn 42 1 43) (SymbolToken ')')
            , MkToken (AlexPn 43 1 44) (SymbolToken '-')
            , MkToken (AlexPn 44 1 45) (SymbolToken '(')
            , MkToken (AlexPn 45 1 46) (IntToken 2)
            , MkToken (AlexPn 46 1 47) (SymbolToken '+')
            , MkToken (AlexPn 47 1 48) (SymbolToken '[')
            , MkToken (AlexPn 48 1 49) (SymbolToken ']')
            , MkToken (AlexPn 49 1 50) (SymbolToken ')')
            , MkToken (AlexPn 51 1 52) (IntToken 3)
            , MkToken (AlexPn 52 1 53) (SymbolToken '*')
            , MkToken (AlexPn 53 1 54) (SymbolToken '(')
            , MkToken (AlexPn 54 1 55) (IntToken 4)
            , MkToken (AlexPn 55 1 56) (SymbolToken '+')
            , MkToken (AlexPn 56 1 57) (SymbolToken '[')
            , MkToken (AlexPn 57 1 58) (SymbolToken ']')
            , MkToken (AlexPn 58 1 59) (SymbolToken ')')
            , MkToken (AlexPn 59 1 60) (SymbolToken ')')
            , EOF
            ]
    assertEqual actual (Right expected)
