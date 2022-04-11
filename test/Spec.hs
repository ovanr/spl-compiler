{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}

import Test.Framework
import {-@ HTF_TESTS @-} SPL.Compiler.Lexer.Test
import {-@ HTF_TESTS @-} SPL.Compiler.Parser.Test
import {-@ HTF_TESTS @-} SPL.Compiler.LexerParserComboTest
-- import {-@ HTF_TESTS @-} SPL.Compiler.SemanticAnalysis.TypeCheckPropertyTest
import {-@ HTF_TESTS @-} SPL.Compiler.SemanticAnalysis.TestTypeUnify
import {-@ HTF_TESTS @-} SPL.Compiler.SemanticAnalysis.TestTypeCheck
import {-@ HTF_TESTS @-} SPL.Compiler.SemanticAnalysis.DirBasedTest

main :: IO ()
main = htfMain htf_importedTests
