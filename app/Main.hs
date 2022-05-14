module Main where

import qualified Data.ByteString.Lazy as B
import qualified Data.Text.IO as TIO
import Data.Either.Extra (fromEither)

import Options.Applicative hiding (Parser(..))
import qualified Options.Applicative as OA (Parser(..))

import SPL.Compiler.Main (Options(..), runCompilerMain)

optionsParser :: OA.Parser Options
optionsParser = Options
    <$> argument str (
            metavar "FILENAME" <> 
            help "Input file for compiling")
    <*> strOption (
            short 'o' <> 
            long "output" <> 
            metavar "FILENAME" <> 
            value "-" <>
            help "Output file for writing result")
    <*> pure mempty
    <*> switch (
            long "lexerDump" <>
            short 'l' <>
            help "Only lex file and print the result")
    <*> switch (
            long "parserDump" <>
            short 'p' <>
            help "Only parse file and pretty print the result")
    <*> switch (
            long "typeCheckerDump" <>
            short 't' <>
            help "Parse and typecheck, then pretty print the result")
    <*> switch (
            long "noOptimization" <>
            showDefault <>
            help "Do not perform constant folding and dead code elimination")
    <*> switch (
            long "irDump" <>
            short 'i' <>
            help "Parse, typecheck, transform to intermediate language, then pretty print result")
    <*> switch (
            long "emitSSM" <>
            help "Compile to SSM assembly")
    <*> option auto (
            long "verbosity" <>
            help "The level of verbosity" <>
            showDefault <>
            value 0 <>
            metavar "INT")

runner :: Options -> IO ()
runner opt = do
    s <- B.readFile $ filePath opt
    runCompilerMain opt{ fileContents = s }

main :: IO ()
main = execParser opts >>= runner
  where
    opts = info (optionsParser <**> helper)
      ( fullDesc
     <> progDesc "Compiler for the SPL Language"
     <> header "SPL-compiler")
