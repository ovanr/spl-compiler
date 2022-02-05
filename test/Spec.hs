{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}

import Test.Framework
import {-@ HTF_TESTS @-} SPL.Compiler.Lexer.Test

main :: IO ()
main = htfMain htf_importedTests
