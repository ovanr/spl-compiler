{
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Applicative
import System.Environment
import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Text.Encoding as TE
}

%wrapper "monadUserState-bytestring"

$digit = 0-9 --digits
$alpha = [a-zA-Z] --alphabetic

tokens :-
    <mlc> "*/"                          { begin 0 }
    <mlc> (. # \*)+                     { skip }
    <mlc> .                             { skip }
    <mlc> \n                            { skip }
    <0> "/*"                            { begin mlc }
    <0> $white+                         { skip }
    <0> "--".*                          { skip }
    <0> let                             { \_ _ -> return Let }
    <0> in                              { \_ _ -> return In }
    <0> $digit+                         { token (\ai l -> Int . read . T.unpack $ getCurrentToken ai l) }
    <0> [\=\+\-\*\/\(\)]                { token (\ai l -> Sym . T.head $ getCurrentToken ai l) }
    <0> $alpha [$alpha $digit \_ \']*   { token (\ai l -> Var $ getCurrentToken ai l ) }

{
data Token = 
      Let
    | In 
    | Sym Char
    | Var T.Text
    | Int Int
    | EOF
    deriving (Eq, Show)

alexEOF = return EOF

lazyBStoText :: B.ByteString -> T.Text
lazyBStoText = TE.decodeUtf8 . B.toStrict 

getCurrentToken :: AlexInput -> Int64 -> T.Text
getCurrentToken (_,_,s,_) l = T.take (fromIntegral l) $ lazyBStoText s

getAllResults :: Alex [Token]
getAllResults = do
    x <- alexMonadScanPlus
    case x of
        EOF -> return [x]
        _ -> do
            xs <- getAllResults
            return $ x:xs

data AlexUserState = AlexUserState {
    filePath :: FilePath,
    contents :: B.ByteString 
}

runAlex' :: FilePath -> B.ByteString -> Alex a -> Either T.Text a
runAlex' fp input (Alex f) = 
    case f (AlexState {
                alex_bpos = 0,
                alex_pos  = alexStartPos,
                alex_inp  = input,
                alex_chr  = '\n',
                alex_ust = AlexUserState fp input,
                alex_scd = 0
            }) of 
        Left msg -> Left . T.pack $ msg
        Right ( _, a ) -> Right a

alexMonadScanPlus = do
  inp__@(_,_,_,n) <- alexGetInput
  sc <- alexGetStartCode
  case alexScan inp__ sc of
    AlexEOF -> alexEOF
    AlexError context -> genError context
    AlexSkip  inp__' _len -> do
        alexSetInput inp__'
        alexMonadScanPlus
    AlexToken inp__'@(_,_,_,n') _ action -> let len = n'-n in do
        alexSetInput inp__'
        action (ignorePendingBytes inp__) len

    where
        genError ((AlexPn _ lineno column),c,s,_) = do
            fp <- T.pack <$> alexGetFilePath
            line <- ( (!! (lineno - 1)) . T.lines . lazyBStoText) <$> alexGetContent
            let token = c `T.cons` (T.take 50 . head . T.words . lazyBStoText $ s)
            alexError . T.unpack $  
                fp <> ":" <> T.pack (show lineno) <> ":" <> T.pack (show column) <> 
                ": error: lexical parse error on input '" <> token <> "'\n" <>
                line

alexGetFilePath :: Alex FilePath
alexGetFilePath = 
    Alex $ \s@(AlexState _ _ _ _ _ (AlexUserState fp _)) -> Right (s, fp)

alexGetContent :: Alex B.ByteString
alexGetContent = 
    Alex $ \s@(AlexState _ _ _ _ _ (AlexUserState _ c)) -> Right (s, c)

alexInitUserState = undefined

main = do
    args <- getArgs
    let file = head args
    s <- B.readFile file
    case (runAlex' file s getAllResults) of
        Left err -> TIO.putStrLn err
        Right tokens -> print tokens
}
