module Main where

import qualified Data.ByteString.Lazy as B
import qualified Data.Text.IO as TIO
import Data.Either.Extra (fromEither)

import Options.Applicative hiding (Parser(..))
import qualified Options.Applicative as OA (Parser(..))

import SPL.Compiler.Main (Options(..), compilerMain)

optionsParser :: OA.Parser Options
optionsParser = Options
    <$> strOption (
            long "file" <> 
            metavar "SRC" <> 
            help "Input file for compiling")
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
            long "staticEvaluationDump" <>
            short 's' <>
            help "Parse, typecheck and staticly evaluate expressions, then pretty print the result")
    <*> option auto (
            long "verbosity" <>
            help "The level of verbosity" <>
            showDefault <>
            value 0 <>
            metavar "INT")

runner :: Options -> IO ()
runner opt = do
    s <- B.readFile $ filePath opt
    let result = compilerMain opt{ fileContents = s }
    TIO.putStrLn . fromEither $ result

main :: IO ()
main = execParser opts >>= runner
  where
    opts = info (optionsParser <**> helper)
      ( fullDesc
     <> progDesc "Compiler for the SPL Language"
     <> header "SPL-compiler")
