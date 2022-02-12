{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

#define ALEX_MONAD_BYTESTRING

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
