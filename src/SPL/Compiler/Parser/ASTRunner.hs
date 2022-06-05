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
        info = "The error occurred while attempting to parse a " <> last (init xs)
        extraInfo = "The parsing branch is as follows: " 
        branch = "    " <> (T.intercalate " -> " . init $ xs)
        err = last xs
      in T.init $ T.unlines [header, "", info, extraInfo, branch, err]


performParsing :: [Token] -> FilePath -> [Text] -> Either Text AST
performParsing tokens path source = do
    let state = ParserState 0 tokens path source
    case runParser pAST state of
        (Nothing, Nothing) -> Left "Internal parser failure." 
        (Nothing, Just err) -> Left . printParserError . errMsg $ err
        (Just (res, _), _) -> Right res
