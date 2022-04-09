{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use camelCase" #-}

module SPL.Compiler.TypeChecker.DirBasedTest (htf_thisModulesTests) where

import Test.Framework 
import Data.Either
import Control.Monad
import Data.Text.Encoding (encodeUtf8)
import Data.ByteString.Lazy (fromStrict)
import qualified Data.ByteString.Lazy as B
import System.Directory

import SPL.Compiler.Main (compilerMain, Options(..))


inputDir = "test/SPL/Compiler/TypeChecker/input_ok/"
outputDir = "test/SPL/Compiler/TypeChecker/output_ok/"
failingDir = "test/SPL/Compiler/TypeChecker/input_failing/"

testTuples :: IO [(FilePath, FilePath)]
testTuples = do
    test_files <- getDirectoryContents inputDir
    return [ (inputDir <> file, outputDir <> file) | file <- test_files, file /= "." && file /= ".." ]

failingInputs :: IO [FilePath]
failingInputs = do
    test_files <- getDirectoryContents failingDir
    return [ failingDir <> file | file <- test_files, file /= "." && file /= ".." ]


-- test_type_check_intergration_test = do
--     tuples <- testTuples
--     forM_ tuples $ \(input_path, expected_output_path) -> do
--         print input_path
--         print expected_output_path
--         input <- B.readFile input_path
--         let actual_output = compilerMain $ Options input_path input False False True 0

--         assertRight actual_output

--         let input_encoded = fromStrict . encodeUtf8 . fromRight mempty $ actual_output
--         expected_output <- B.readFile expected_output_path
--         assertEqual input_encoded expected_output

test_type_check_expected_failures = do
    failing_input_paths <- failingInputs
    forM_ failing_input_paths $ \input_path -> do
        print input_path
        input <- B.readFile input_path
        let options = Options input_path input False False True 0
        let checked_input = compilerMain options
        assertLeft checked_input
