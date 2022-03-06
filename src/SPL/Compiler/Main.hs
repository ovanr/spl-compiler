{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.Main where

import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import Control.Lens (maximumOf, _Left, folded)
import Data.Text (Text)
import Data.Either
import Data.Maybe

import SPL.Compiler.Lexer.AlexLexGen (tokenize)
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..), Error(..))
import SPL.Compiler.Parser.ASTParser 
import SPL.Compiler.Parser.ASTPrettyPrint (PrettyPrint(..))

data Options = Options {
    filePath :: FilePath,
    fileContents :: B.ByteString,
    lexerDump :: Bool,
    parserDump :: Bool,
    verbosity :: Int
}

compilerMain :: Options -> Either Text Text
compilerMain (Options path content lexDump parserDump v) = do
    tokens <- tokenize path content
    let state = ParserState 0 tokens
    if lexDump then
        Right . T.pack . show $ tokens
    else do
        ast <- case runParser pAST state of
            [] -> Left "Internal parser error: Parser did not return any results"
            xs | null (rights xs) -> Left . errMsg . fromJust $ maximumOf (folded._Left) xs
               | otherwise -> Right . fst . head $ rights xs

        if parserDump then
            Right . toCode 0 $ ast
        else
            Left "Not implemented"
