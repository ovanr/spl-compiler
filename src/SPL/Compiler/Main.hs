{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.Main where

import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import Data.Text.Encoding (decodeUtf8)
import Control.Lens (maximumOf, _Left, folded)
import Data.Text (Text)
import Data.Foldable
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

printError :: [Text] -> Text
printError [] = mempty
printError xs =
    let header = "Error occurred during parsing phase!"
        info = "Best match parse branch:  " <> (T.intercalate " -> " . init $ xs)
        err = last xs
      in T.init $ T.unlines [header, info, err]

compilerMain :: Options -> Either Text Text
compilerMain (Options path content lexDump parserDump v) = do
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
            Right . toCode 0 $ ast
        else
            Left "Not implemented"
