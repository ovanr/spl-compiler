{
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.Lexer.AlexLexGen 
    (
    tokenize, 
    Token(..),
    SPLToken(..), 
    Type(..),
    Keyword(..), 
    AlexPosn(..),
    ) where

import Control.Applicative
import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
}

-- TODO: support nestsed nested block-comments

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
    <mlc> "*/"                           { \c l -> decMLCDepth >> getMLCDepth >>= (\d -> if d == 0 then begin 0 c l else alexMonadScan) }
    -- <mlc> (. # \*)+                      { skip } */
    <mlc> .                              { skip }
    <mlc> \n                             { skip }
    <mlc> "/*"                           { \c l -> incMLCDepth >> skip c l }

    
    <0> "/*"                             { \c l -> startMLCDepth >> begin mlc c l }
    <0> $white+                          { skip }
    <0> "//".*                           { skip }

    -- keywords
    <0> "var"                            { \ctx len -> return $ produceToken (\_ _ -> KeywordToken Var) ctx len}
    <0> "if"                             { \ctx len -> return $ produceToken (\_ _ -> KeywordToken If) ctx len}
    <0> "else"                           { \ctx len -> return $ produceToken (\_ _ -> KeywordToken Else) ctx len}
    <0> "while"                          { \ctx len -> return $ produceToken (\_ _ -> KeywordToken While) ctx len}
    <0> "return"                         { \ctx len -> return $ produceToken (\_ _ -> KeywordToken Return)ctx len}

    -- types
    <0> "Void"                           { \ctx len -> return $ produceToken (\_ _ -> TypeToken VoidType) ctx len}
    <0> "Char"                           { \ctx len -> return $ produceToken (\_ _ -> TypeToken CharType) ctx len}
    <0> "Bool"                           { \ctx len -> return $ produceToken (\_ _ -> TypeToken BoolType) ctx len}
    <0> "Int"                            { \ctx len -> return $ produceToken (\_ _ -> TypeToken IntType) ctx len}

    -- `token` function simply takes passes the lexer context and token length
    -- to the function given and liftes the result to AlexAction

    -- symbols
    <0> [\!\:\|\&\=\>\<\%\*\-\+\{\}\;\.\,\^\-\(\)\[\]\/]  { token (produceToken (\ctx len -> SymbolToken . T.head $ getCurrentToken ctx len )) }


    -- Bool
    <0> "True"                            { \ctx len -> return $ produceToken (\_ _ -> BoolToken True) ctx len}
    <0> "False"                           { \ctx len -> return $ produceToken (\_ _ -> BoolToken False) ctx len}

    -- int
    <0> $digit+                          { token (produceToken (\ctx len -> IntToken . read . T.unpack $ getCurrentToken ctx len)) }

    -- id
    <0> $alpha [$alpha $digit \_ \']*    { token (produceToken (\ctx len -> IdentifierToken $ getCurrentToken ctx len )) }

    -- character
    <0> \'.\'                            { token (produceToken (\ctx len -> CharToken $ flip T.index 1 $ getCurrentToken ctx len )) }
    <0> \'\\.\'                          { token (produceToken (\ctx len -> CharToken $ flip T.index 1 $ getCurrentToken ctx len )) }

    -- strings
    <0> \".*\"                            { token (produceToken (\ctx len -> StringToken . T.dropEnd 1 .  T.drop 1 $ getCurrentToken ctx len )) }
{

-- token :: (AlexInput -> Int64 -> token) -> AlexAction token

getAlexUserState :: Alex AlexUserState
getAlexUserState = Alex $ \s@(AlexState _ _ _ _ _ u) -> Right (s,u)

setAlexUserState :: AlexUserState -> Alex ()
setAlexUserState u = Alex $ \s@(AlexState a b c d e _) -> Right (AlexState a b c d e u, ())

getMLCDepth :: Alex Int
getMLCDepth = getAlexUserState >>= (\(AlexUserState _ _ depth) -> pure depth)

startMLCDepth :: Alex ()
startMLCDepth = getAlexUserState >>= (\(AlexUserState a b depth) -> setAlexUserState (AlexUserState a b 1))

incMLCDepth :: Alex ()
incMLCDepth = getAlexUserState >>= (\(AlexUserState a b depth) -> setAlexUserState (AlexUserState a b (depth + 1)))

decMLCDepth :: Alex ()
decMLCDepth = getAlexUserState >>= (\(AlexUserState a b depth) -> setAlexUserState (AlexUserState a b (depth - 1)))

-- produce Token with position
produceToken :: (AlexInput -> Int64 -> SPLToken) -> AlexInput -> Int64 -> Token
produceToken f ctx len = MkToken (getCurrentPosn ctx) (f ctx len)

data Token =
      MkToken AlexPosn SPLToken
    | EOF
    deriving (Eq, Show)

data SPLToken = 
      KeywordToken Keyword
    | TypeToken Type
    | SymbolToken Char
    | StringToken T.Text
    | IntToken Integer
    | CharToken Char
    | BoolToken Bool
    | IdentifierToken T.Text
    deriving (Eq)

data Keyword =
      Var
    | If
    | Else
    | While
    | Return
    deriving (Eq)

data Type =
      IntType
    | BoolType
    | CharType
    | VoidType
    deriving (Eq)

instance Show Type where
    show IntType = "Int"
    show BoolType = "Bool"
    show CharType = "Char"
    show VoidType = "Void"

instance Show Keyword where
    show Var = "var"
    show If = "if"
    show Else = "else"
    show While = "while"
    show Return = "return"

instance Show SPLToken where
    show (KeywordToken k) = show k
    show (TypeToken t) = show t
    show (SymbolToken c) = [c]
    show (StringToken str) = T.unpack str
    show (IntToken i) = show i
    show (CharToken c) = show c
    show (BoolToken b) = show b
    show (IdentifierToken i) = T.unpack i

alexEOF = return EOF

-- Convert a Lazy Bytestring to Text
lazyBStoText :: B.ByteString -> T.Text
lazyBStoText = TE.decodeUtf8 . B.toStrict 

-- Get the current parsed token as T.Text
getCurrentToken :: AlexInput -> Int64 -> T.Text
getCurrentToken (_,_,s,_) l = T.take (fromIntegral l) $ lazyBStoText s

getCurrentPosn :: AlexInput -> AlexPosn
getCurrentPosn (pos,_,_,_) = pos

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
    contents :: B.ByteString, 
    multiLineCommentDepth :: Int
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
                ["Error occurred during lexing phase!", 
                header <> "Unrecognised input '" <> token <> "'", 
                T.replicate gap " " <> "|", 
                T.pack (show lineno) <> " | " <> line, 
                T.replicate gap " " <> "|" <> bottomHighlight
                ] 

-- Getter for the filepath from the user state 
alexGetFilePath :: Alex FilePath
alexGetFilePath = 
    Alex $ \s@(AlexState _ _ _ _ _ (AlexUserState fp _ _)) -> Right (s, fp)

--   Getter for the file content from the user state 
alexGetContent :: Alex B.ByteString
alexGetContent = 
    Alex $ \s@(AlexState _ _ _ _ _ (AlexUserState _ c _)) -> Right (s, c)

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
            alex_ust = AlexUserState fp input 0, 
            alex_scd = 0 
        } 

}
