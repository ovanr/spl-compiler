{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.Main where

import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import Data.Text.Encoding (decodeUtf8)
import Control.Lens (maximumOf, _Left, folded)
import Control.Monad.State (StateT(StateT, runStateT), evalStateT)
import Data.Text (Text)
import Data.Foldable
import Data.Either
import Data.Bifunctor
import Data.Functor
import Control.Monad
import Data.Maybe

import SPL.Compiler.Common.TypeFunc

import SPL.Compiler.Lexer.AlexLexGen (tokenize)
import SPL.Compiler.Parser.ASTRunner
import qualified SPL.Compiler.Parser.ASTPrettyPrint as ASTPP (PrettyPrint(..))

import qualified SPL.Compiler.SemanticAnalysis.TCTPrettyPrint as TCTPP (PrettyPrint(..))
import SPL.Compiler.SemanticAnalysis.SemanticAnalysis

import SPL.Compiler.CodeGen.CoreLang
import SPL.Compiler.CodeGen.CoreLangGen
import SPL.Compiler.CodeGen.CoreLangGenLib
import SPL.Compiler.CodeGen.CoreLangPrinter

import SPL.Compiler.CodeGen.Backend.SSMGen

data Options = Options {
    filePath :: FilePath,
    fileContents :: B.ByteString,
    lexerDump :: Bool,
    parserDump :: Bool,
    typeCheckDump :: Bool,
    noStaticEvaluation :: Bool,
    coreLangDump :: Bool,
    emitSSM :: Bool,
    verbosity :: Int
}

compilerMain :: Options -> Either Text Text
compilerMain (Options path content lexDump parserDump typeCheckDump noStaticEvaluation coreLangDump emitSSM v) = do
    tokens <- tokenize path content
    let source = T.lines . decodeUtf8 . B.toStrict $ content
    when lexDump $
        Left . T.pack . show $ tokens

    ast <- performParsing tokens path source
    when parserDump $
        Left . ASTPP.toCode 0 $ ast
    
    tct <- performSemanticAnalysis noStaticEvaluation ast path source
    when typeCheckDump $
        Left . TCTPP.toCode 0 $ tct
    
    Some2 core <- performCoreLangGen tct
    when coreLangDump $
            Left $ showCL 0 core

    if emitSSM then do
        ssm <- produceSSM core
        Right $ T.unlines ssm
    else
        Left "Not implemented"
