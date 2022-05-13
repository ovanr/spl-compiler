{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.Parser.ASTRunner where

import Data.Text (Text)
import qualified Data.Text as T
import Control.Lens
import Data.Either
import Data.Maybe

import SPL.Compiler.Lexer.AlexLexGen (Token)
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..), Error(..))
import SPL.Compiler.Parser.ASTParser
import SPL.Compiler.Parser.AST
import qualified SPL.Compiler.Parser.ASTPrettyPrint as ASTPP (PrettyPrint(..))

printParserError :: [Text] -> Text
printParserError [] = mempty
printParserError xs =
    let header = "Error occurred during parsing phase!"
        info = "Best match parse branch:  " <> (T.intercalate " -> " . init $ xs)
        err = last xs
      in T.init $ T.unlines [header, "", info, err]


performParsing :: [Token] -> FilePath -> [Text] -> Either Text AST
performParsing tokens path source = do
    let state = ParserState 0 tokens path source
    case runParser pAST state of
        [] -> Left "Internal parser error: Parser did not return any results"
        xs | null (rights xs) -> Left . printParserError . errMsg . fromJust $ maximumOf (folded._Left) xs
           | otherwise -> Right . fst . head $ rights xs
