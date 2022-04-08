{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}

module SPL.Compiler.TypeChecker.DirBasedTest (htf_thisModulesTests) where

import Test.Framework 
import Data.Either
import Control.Monad
import Data.Text.Encoding (encodeUtf8)
import Data.ByteString.Lazy (fromStrict)

import qualified Data.ByteString.Lazy as B

import SPL.Compiler.Main (compilerMain, Options(..))

import System.Directory

input_dir = "test/SPL/Compiler/TypeChecker/input_ok/"
output_dir = "test/SPL/Compiler/TypeChecker/output_ok/"
failing_dir = "test/SPL/Compiler/TypeChecker/input_failing/"

test_tuples :: IO [(FilePath, FilePath)]
test_tuples = do
    test_files <- getDirectoryContents input_dir
    return [ (input_dir <> file, output_dir <> file) | file <- test_files, file /= "." && file /= ".." ]

failing_inputs :: IO [FilePath]
failing_inputs = do
    test_files <- getDirectoryContents failing_dir
    return [ failing_dir <> file | file <- test_files, file /= "." && file /= ".." ]



-- property check of the form: 
-- parsing a file two times is semantically equivalent to parsing one time
--  compilerMain { compilerMain { TEST_FILE, parserDump }, parserDump } == compilerMain { TEST_FILE, parserDump }
test_type_check_property_check = do
    tuples <- test_tuples
    forM_ tuples $ \(input_path, output_path) -> do
        print input_path
        print output_path
        input <- B.readFile input_path
        let options = Options input_path input False False True 0
        let checked_input = compilerMain options
        when (isLeft checked_input) $ print $ "---> " <> input_path
        when (isRight checked_input) $ do
            let input_encoded = fromStrict . encodeUtf8 . fromRight mempty $ checked_input
            output <- B.readFile output_path
            assertEqual input_encoded output

    failing_input_paths <- failing_inputs
    forM_ failing_input_paths $ \input_path -> do
        print input_path
        input <- B.readFile input_path
        let options = Options input_path input False False True 0
        let checked_input = compilerMain options
        assertLeft checked_input
    
