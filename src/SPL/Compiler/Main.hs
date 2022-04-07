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
import SPL.Compiler.TypeChecker.TCT(TCT(..), Error)

import Control.Monad.State (StateT(StateT, runStateT))
import SPL.Compiler.TypeChecker.TypeCheck (typeCheckTCT, TypeCheckState (TypeCheckState))
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

printError :: [Text] -> Text
printError [] = mempty
printError xs =
    let header = "Error occurred during parsing phase!"
        info = "Best match parse branch:  " <> (T.intercalate " -> " . init $ xs)
        err = last xs
      in T.init $ T.unlines [header, info, err]

compilerMain :: Options -> Either Text Text
compilerMain (Options path content lexDump parserDump typeCheckDump v) = do
    tokens <- tokenize path content
    let state = ParserState 0 tokens path (T.lines . decodeUtf8 . B.toStrict $ content)
    if lexDump then
        Right . T.pack . show $ tokens
    else do
        ast <- case runParser pAST state of
            [] -> Left "Internal parser error: Parser did not return any results"
            xs | null (rights xs) -> Left . printError . errMsg . fromJust $ maximumOf (folded._Left) xs
               | otherwise -> Right . fst . head $ rights xs

        if parserDump then
            Right . ASTPP.toCode 0 $ ast
        else
            do
            initTCT <- Right . ast2tct $ ast
            checkedTCT <- first (T.intercalate "\n") $ runStateT (typeCheckTCT initTCT) (TypeCheckState 0)
            if typeCheckDump then
                Right . TCTPP.toCode 0 $ fst checkedTCT
            else
                Left "Not implemented"

