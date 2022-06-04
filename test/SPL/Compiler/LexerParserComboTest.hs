{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}

module SPL.Compiler.LexerParserComboTest (htf_thisModulesTests) where

import Test.Framework 
import Data.Either
import Control.Monad.Trans.Except
import Control.Monad.State
import Control.Monad
import Data.Text.Encoding (encodeUtf8)
import Data.ByteString.Lazy (fromStrict)

import qualified Data.ByteString.Lazy as B

import SPL.Compiler.Main (compilerMain, Options(..))

sourceFiles = [
    "test/SPL/Compiler/source_files/2D.spl",
    "test/SPL/Compiler/source_files/Example.spl",
    "test/SPL/Compiler/source_files/mutrec.spl",
    "test/SPL/Compiler/source_files/shadow.spl",
    "test/SPL/Compiler/source_files/3D.spl",                      
    "test/SPL/Compiler/source_files/op.spl",
    "test/SPL/Compiler/source_files/a_bit_of_everything.spl",
    "test/SPL/Compiler/source_files/identity.spl",
    "test/SPL/Compiler/source_files/overloading.spl",
    "test/SPL/Compiler/source_files/stress.spl",
    "test/SPL/Compiler/source_files/arguments.spl",
    "test/SPL/Compiler/source_files/infinite_type_shouldfail.spl",
    "test/SPL/Compiler/source_files/polymorphic_value_again_shouldfail.spl",
    "test/SPL/Compiler/source_files/stress_test.spl",
    "test/SPL/Compiler/source_files/assignment_to_builtin.spl",
    "test/SPL/Compiler/source_files/integers.spl",
    "test/SPL/Compiler/source_files/polymorphic_value_indirect_shouldfail.spl",
    "test/SPL/Compiler/source_files/SumProduct.spl",
    "test/SPL/Compiler/source_files/bool.spl",
    -- "test/SPL/Compiler/source_files/list_ops.spl",
    "test/SPL/Compiler/source_files/polymorphic_value_shouldfail.spl",
    "test/SPL/Compiler/source_files/sum.spl",
    -- "test/SPL/Compiler/source_files/brainfuck.spl",
    "test/SPL/Compiler/source_files/list.spl",
    "test/SPL/Compiler/source_files/problematic_programs.spl",
    "test/SPL/Compiler/source_files/unary_minus.spl",
    "test/SPL/Compiler/source_files/comment.spl",
    "test/SPL/Compiler/source_files/lists.spl",
    "test/SPL/Compiler/source_files/problematic.spl",
    -- "test/SPL/Compiler/source_files/unbalanced_parenthesis2.spl",
    "test/SPL/Compiler/source_files/complete.spl",
    "test/SPL/Compiler/source_files/many_parenthesis.spl",
    "test/SPL/Compiler/source_files/many_parenthesis2.spl",
    "test/SPL/Compiler/source_files/recursion.spl",
    -- "test/SPL/Compiler/source_files/unbalanced_parenthesis.spl",
    "test/SPL/Compiler/source_files/constants_corner_cases.spl",
    -- "test/SPL/Compiler/source_files/monomorph.spl",
    "test/SPL/Compiler/source_files/return_ill_typed.spl",
    "test/SPL/Compiler/source_files/while.spl",
    "test/SPL/Compiler/source_files/constants.spl",
    "test/SPL/Compiler/source_files/more_parenthesis.spl",
    "test/SPL/Compiler/source_files/return_in_all_code_paths.spl",
    "test/SPL/Compiler/source_files/whitespaces.spl",
    "test/SPL/Compiler/source_files/cyclic.spl",
    "test/SPL/Compiler/source_files/multiple_recursion.spl",
    "test/SPL/Compiler/source_files/return_well_typed.spl",
    -- "test/SPL/Compiler/source_files/x.spl",
    -- "test/SPL/Compiler/source_files/empty.spl",
    "test/SPL/Compiler/source_files/multiple_recursion_values.spl",
    "test/SPL/Compiler/source_files/self_application_shouldfail.spl"]

-- property check of the form: 
-- parsing a file two times is semantically equivalent to parsing one time
--  compilerMain { compilerMain { TEST_FILE, parserDump }, parserDump } == compilerMain { TEST_FILE, parserDump }
test_parser_property_check = do
    forM_ sourceFiles $ \fp -> do
        contents <- B.readFile fp
        let options = Options fp "-" contents False True False False
        print fp
        pass1 <- (fmap fst) <$> runExceptT (runStateT compilerMain options)
        when (isLeft pass1) $ print $ "---> " <> fp
        when (isRight pass1) $ do
            let contentNew = fromStrict . encodeUtf8 . fromRight mempty $ pass1
            pass2 <- fmap fst <$> runExceptT (runStateT compilerMain options{ fileContents = contentNew })
            assertEqual pass1 pass2
