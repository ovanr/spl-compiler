{
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.Lexer.AlexLexGen 
    (
    tokenize, 
    Token(..), 
    Symbol(..), 
    Type(..),
    Keyword(..), 
    Separator(..),
    Operator(..)
    ) where

import Control.Applicative
import System.Environment
import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Text.Encoding as TE
}

-- this wrapper generates the Alex data type 
-- which is a state monad with possibility of failure
-- see the generated file for its definition
-- Alex :: AlexState -> Either String (AlexState, a)
%wrapper "monadUserState-bytestring"

$digit = 0-9 --digits
$alpha = [a-zA-Z] --alphabetic

tokens :-
    -- mlc, 0 are startcodes 
    -- these define the 'state' we are in
    -- e.g. if we see */ then we enter the mlc state
    -- and only rules that start with mlc are taken into account
    -- otherwise we are at the default 0 state
    <mlc> "*/"                           { begin 0 }
    <mlc> (. # \*)+                      { skip }
    <mlc> .                              { skip }
    <mlc> \n                             { skip }

    
    <0> "/*"                             { begin mlc }
    <0> $white+                          { skip }
    <0> "//".*                           { skip }

    -- keywords
    <0> "var"                            { \_ _ -> return $ KeywordToken Var }
    <0> "if"                             { \_ _ -> return $ KeywordToken If }
    <0> "else"                           { \_ _ -> return $ KeywordToken Else }
    <0> "while"                          { \_ _ -> return $ KeywordToken While }
    <0> "return"                         { \_ _ -> return $ KeywordToken Return }

    -- types
    <0> "Void"                           { \_ _ -> return $ TypeToken VoidType }
    <0> "Char"                           { \_ _ -> return $ TypeToken CharType }
    <0> "Bool"                           { \_ _ -> return $ TypeToken BoolType }
    <0> "Int"                            { \_ _ -> return $ TypeToken IntType }

    -- symbols
    <0> "["                              { \_ _ -> return $ SymbolToken SquareBracketOpen}
    <0> "]"                              { \_ _ -> return $ SymbolToken SquareBracketClosed}
    <0> "("                              { \_ _ -> return $ SymbolToken BracketOpen}
    <0> ")"                              { \_ _ -> return $ SymbolToken BracketClosed}
    <0> "->"                             { \_ _ -> return $ SymbolToken RightArrow}
    <0> "::"                             { \_ _ -> return $ SymbolToken DoubleColon}
    <0> ","                              { \_ _ -> return $ SymbolToken Comma}
    <0> "."                              { \_ _ -> return $ SymbolToken Dot}

    -- separator
    <0> ";"                              { \_ _ -> return $ SeparatorToken Semicolon}
    <0> "{"                              { \_ _ -> return $ SeparatorToken CurlyBraceOpen}
    <0> "}"                              { \_ _ -> return $ SeparatorToken CurlyBraceClosed}

    -- operator
    <0> "+"                              { \_ _ -> return $ OperatorToken Plus}
    <0> "-"                              { \_ _ -> return $ OperatorToken Minus}
    <0> "*"                              { \_ _ -> return $ OperatorToken Star}
    <0> "/"                              { \_ _ -> return $ OperatorToken Slash}
    <0> "%"                              { \_ _ -> return $ OperatorToken Percent}
    <0> "="                              { \_ _ -> return $ OperatorToken Equal}
    <0> "=="                             { \_ _ -> return $ OperatorToken DoubleEqual}
    <0> "<"                              { \_ _ -> return $ OperatorToken Less}
    <0> ">"                              { \_ _ -> return $ OperatorToken Greater}
    <0> "<="                             { \_ _ -> return $ OperatorToken LessOrEqual}
    <0> ">="                             { \_ _ -> return $ OperatorToken GreaterOrEqual}
    <0> "!="                             { \_ _ -> return $ OperatorToken NotEqual}
    <0> "&&"                             { \_ _ -> return $ OperatorToken DoubleAnd}
    <0> "||"                             { \_ _ -> return $ OperatorToken DoublePipe}
    <0> ":"                              { \_ _ -> return $ OperatorToken SingleColon}
    <0> "!"                              { \_ _ -> return $ OperatorToken ExclamationMark}

    -- int
    <0> "-"?$digit+                      { token (\ai l -> IntToken . read . T.unpack $ getCurrentToken ai l) }

    -- id
    <0> $alpha [$alpha $digit \_ \']*    { token (\ai l -> IdentifierToken $ getCurrentToken ai l ) }

{

data Token = 
      KeywordToken Keyword
    | TypeToken Type
    | SymbolToken Symbol
    | SeparatorToken Separator
    | OperatorToken Operator
    | IntToken Int
    | IdentifierToken T.Text
    | EOF
    deriving (Eq, Show)

data Keyword =
      Var
    | If
    | Else
    | While
    | Return
    deriving (Eq, Show)

data Type =
      IntType
    | BoolType
    | CharType
    | VoidType
    deriving (Eq, Show)

data Symbol = 
      SquareBracketOpen
    | SquareBracketClosed
    | BracketOpen
    | BracketClosed
    | RightArrow
    | DoubleColon
    | Comma
    | Dot
    deriving (Eq, Show)

-- ; { } 
data Separator =
      Semicolon
    | CurlyBraceOpen
    | CurlyBraceClosed
    deriving (Eq, Show)

data Operator =
      Plus
    | Minus
    | Star
    | Slash
    | Percent
    | Equal
    | DoubleEqual
    | Less
    | Greater
    | LessOrEqual
    | GreaterOrEqual
    | NotEqual
    | DoubleAnd
    | DoublePipe
    | SingleColon
    | ExclamationMark
    deriving (Eq, Show)


alexEOF = return EOF

-- Convert a Lazy Bytestring to Text
lazyBStoText :: B.ByteString -> T.Text
lazyBStoText = TE.decodeUtf8 . B.toStrict 

-- Get the current parsed token as T.Text
getCurrentToken :: AlexInput -> Int64 -> T.Text
getCurrentToken (_,_,s,_) l = T.take (fromIntegral l) $ lazyBStoText s

-- Retrieve all tokens.
-- Note that failures are automatically captured by the Alex monad instance.
-- i.e. we get (Left err) and thus the bind (>>=) operator short-circuits
getAllResults :: Alex [Token]
getAllResults = do
    x <- alexMonadScan'
    case x of
        EOF -> return [x]
        _ -> do
            xs <- getAllResults
            return $ x:xs

-- Pass in additional state to the Lexer.
-- The current filepath and the file contents
-- are used to give us nicer error messages
data AlexUserState = AlexUserState { 
    filePath :: FilePath, 
    contents :: B.ByteString 
}


-- Parse a single token.
-- Identical to generated alexMonadScan function
-- but with nicer error message (AlexError match)
alexMonadScan' = do
  inp__@(_,_,_,n) <- alexGetInput
  sc <- alexGetStartCode
  case alexScan inp__ sc of
    AlexEOF -> alexEOF
    AlexError context -> genError context
    AlexSkip  inp__' _len -> do
        alexSetInput inp__'
        alexMonadScan'
    AlexToken inp__'@(_,_,_,n') _ action -> let len = n'-n in do
        alexSetInput inp__'
        action (ignorePendingBytes inp__) len

    where
        genError ((AlexPn _ lineno column),c,s,_) = do
            fp <- T.pack <$> alexGetFilePath
            line <- ( (!! (lineno - 1)) . T.lines . lazyBStoText) <$> alexGetContent
            let token = T.take 50 . head . T.words . lazyBStoText $ s
                header = fp <> ":" <> T.pack (show lineno) <> ":" <> T.pack (show column) <> ": "
                gap = 1 + (length $ show lineno)
                bottomHighlight = T.replicate (column) " " <> T.replicate (T.length token) "^"
            alexError . T.unpack . T.unlines $ 
                [  
                header <> "error: lexical parse failure on input '" <> token <> "'", 
                T.replicate gap " " <> "|", 
                T.pack (show lineno) <> " | " <> line, 
                T.replicate gap " " <> "|" <> bottomHighlight
                ] 

-- Getter for the filepath from the user state 
alexGetFilePath :: Alex FilePath
alexGetFilePath = 
    Alex $ \s@(AlexState _ _ _ _ _ (AlexUserState fp _)) -> Right (s, fp)

--   Getter for the file content from the user state 
alexGetContent :: Alex B.ByteString
alexGetContent = 
    Alex $ \s@(AlexState _ _ _ _ _ (AlexUserState _ c)) -> Right (s, c)

-- Needed by the generated runAlex function.
-- Note that we don't use that function thus it can be left undefined
alexInitUserState = undefined

-- Runner of the lexer.
-- Takes the filepath and its contents
-- and returns a failure message or a list of tokens
tokenize :: FilePath -> B.ByteString -> Either T.Text [Token]
tokenize fp input = 
    case (unAlex getAllResults) state of
        Left msg -> Left . T.pack $ msg
        Right ( _, a ) -> Right a
    where
        state = AlexState { 
            alex_bpos = 0, 
            alex_pos  = alexStartPos, 
            alex_inp  = input, 
            alex_chr  = '\n', 
            alex_ust = AlexUserState fp input, 
            alex_scd = 0 
        } 

-- Parse the file given by the first cli argument 
main = do
    args <- getArgs
    let file = head args
    s <- B.readFile file
    case (tokenize file s) of
        Left err -> TIO.putStr err
        Right tokens -> print tokens
}
