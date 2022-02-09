{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module SPL.Compiler.Lexer.Test (htf_thisModulesTests) where

import Test.Framework
import SPL.Compiler.Lexer.AlexLexGen (tokenize, Token(..), Keyword(..))
import qualified Data.ByteString.Lazy as B

tokenize_file fl = do
    contents <- B.readFile fl
    return $ tokenize fl contents
    
test_tokenize_at_sign_in_identifier = do
    actual <- tokenize_file "test/SPL/Compiler/Lexer/at_sign_in_id.spl"
    assertLeft actual

test_tokenize_multi_line_comment = do
    actual <- tokenize_file "test/SPL/Compiler/Lexer/multi_line_comment.spl"
    let expected = [KeywordToken While, 
                    IdentifierToken "id23", 
                    IdentifierToken "how", 
                    IntToken 233, 
                    IdentifierToken "okay",
                    EOF]
    
    assertEqual actual (Right expected)
