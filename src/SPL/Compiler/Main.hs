{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.Main where

import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import Data.Text.Encoding (decodeUtf8)
import Control.Lens (maximumOf, _Left, folded)
import Data.Text (Text)
import Data.Foldable
import Data.Either
import Data.Bifunctor
import Data.Maybe

import SPL.Compiler.Lexer.AlexLexGen (tokenize)
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..), Error(..))
import SPL.Compiler.Parser.ASTParser
import qualified SPL.Compiler.Parser.ASTPrettyPrint as ASTPP (PrettyPrint(..))
import SPL.Compiler.TypeChecker.TCT(TCT(..), Error, TypeCheckState(..))

import Control.Monad.State (StateT(StateT, runStateT))
import SPL.Compiler.TypeChecker.TypeCheck (typeCheckTCT)
import SPL.Compiler.TypeChecker.TreeTransformer (ast2tct)
import qualified SPL.Compiler.TypeChecker.TCTPrettyPrint as TCTPP (PrettyPrint(..))

data Options = Options {
    filePath :: FilePath,
    fileContents :: B.ByteString,
    lexerDump :: Bool,
    parserDump :: Bool,
    typeCheckDump :: Bool,
    verbosity :: Int
}

printParserError :: [Text] -> Text
printParserError [] = mempty
printParserError xs =
    let header = "Error occurred during parsing phase!"
        info = "Best match parse branch:  " <> (T.intercalate " -> " . init $ xs)
        err = last xs
      in T.init $ T.unlines [header, "", info, err]

printTypeCheckError :: [Text] -> Text
printTypeCheckError [] = mempty
printTypeCheckError errors =
    let header = "Error occurred during type checking phase!"
      in T.init $ T.unlines $ header: "": errors

compilerMain :: Options -> Either Text Text
compilerMain (Options path content lexDump parserDump typeCheckDump v) = do
    tokens <- tokenize path content
    let source = T.lines . decodeUtf8 . B.toStrict $ content
    let state = ParserState 0 tokens path source
    if lexDump then
        Right . T.pack . show $ tokens
    else do
        ast <- case runParser pAST state of
            [] -> Left "Internal parser error: Parser did not return any results"
            xs | null (rights xs) -> Left . printParserError . errMsg . fromJust $ maximumOf (folded._Left) xs
               | otherwise -> Right . fst . head $ rights xs

        if parserDump then
            Right . ASTPP.toCode 0 $ ast
        else do
            let tcState = TypeCheckState 0 path source
            initTCT <- Right . ast2tct $ ast
            tct <- case runStateT (typeCheckTCT initTCT) tcState of
                Left err -> Left . printTypeCheckError $ err
                Right (tct, _) -> Right tct

            if typeCheckDump then
                Right . TCTPP.toCode 0 $ tct
            else
                Left "Not implemented"
