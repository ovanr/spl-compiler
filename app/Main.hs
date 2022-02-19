module Main where

import qualified Data.ByteString.Lazy as B
import qualified Data.Text.IO as TIO
import System.Environment (getArgs)

import SPL.Compiler.Lexer.AlexLexGen (tokenize)

main :: IO ()
main = do
    args <- getArgs
    let file = head args
    s <- B.readFile file
    case tokenize file s of
        Left err -> TIO.putStr err
        Right tokens -> print tokens
