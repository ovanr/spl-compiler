{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.Main where

import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Text.Encoding (decodeUtf8)
import Control.Lens (maximumOf, _Left, folded)
import Control.Monad.State (StateT(StateT, runStateT), evalStateT, gets)
import Control.Monad.Trans
import Data.Text (Text)
import Data.Foldable
import Data.Either
import Data.Bifunctor
import Data.Functor
import Control.Monad
import Data.Maybe
import System.IO

import SPL.Compiler.Common.TypeFunc
import Control.Monad.Trans.Except

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

runCompilerMain :: Options -> IO ()
runCompilerMain options = do
    res <- fmap fst <$> runExceptT (runStateT compilerMain options)
    case res of
        Left err -> TIO.hPutStrLn stderr err
        Right prog -> TIO.hPutStrLn stdout prog

liftEither = lift . ExceptT . pure

compilerMain :: StateT Options (ExceptT Error IO) Text
compilerMain = do
    path' <- gets filePath
    content' <- gets fileContents
    lexerDump' <- gets lexerDump
    parserDump' <- gets parserDump
    typeCheckDump' <- gets typeCheckDump
    noStaticEvaluation' <- gets noStaticEvaluation
    coreLangDump' <- gets coreLangDump
    emitSSM' <- gets emitSSM

    tokens <- liftEither $ tokenize path' content'
    let source = T.lines . decodeUtf8 . B.toStrict $ content'
    if lexerDump' then
        pure . T.pack . show $ tokens
    else do
        ast <- liftEither $ performParsing tokens path' source
        if parserDump' then
            pure . ASTPP.toCode 0 $ ast
        else do
            tct <- lift $ performSemanticAnalysis noStaticEvaluation' ast path' source
            if typeCheckDump' then
                liftEither . Right . TCTPP.toCode 0 $ tct
            else do
                Some2 core <- liftEither $ performCoreLangGen tct
                if coreLangDump' then
                    liftEither . Right $ showCL 0 core
                else do
                    if emitSSM' then do
                        ssm <- liftEither $ produceSSM core
                        pure $ T.unlines ssm
                    else
                        liftEither $ Left "Not implemented"
