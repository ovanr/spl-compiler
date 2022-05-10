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
import Data.Maybe

import SPL.Compiler.Common.TypeFunc

import SPL.Compiler.Lexer.AlexLexGen (tokenize)
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..), Error(..))
import SPL.Compiler.Parser.ASTParser
import qualified SPL.Compiler.Parser.ASTPrettyPrint as ASTPP (PrettyPrint(..))

import SPL.Compiler.SemanticAnalysis.TCT(TCT(..), Error, TypeCheckState(..))
import SPL.Compiler.SemanticAnalysis.TreeTransformer (ast2tct)
import SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis (detectDuplicateFunctionNames)
import SPL.Compiler.SemanticAnalysis.ConstantGlobalVar (globalVarConstantCheck)
import SPL.Compiler.SemanticAnalysis.CallGraphAnalysis (reorderTct)
import SPL.Compiler.SemanticAnalysis.TypeCheck (typeCheckTCT)
import SPL.Compiler.SemanticAnalysis.ReturnPathCheck (returnPathCheck)
import SPL.Compiler.SemanticAnalysis.StaticEvaluation (staticlyEvaluate) 
import qualified SPL.Compiler.SemanticAnalysis.TCTPrettyPrint as TCTPP (PrettyPrint(..))

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

printParserError :: [Text] -> Text
printParserError [] = mempty
printParserError xs =
    let header = "Error occurred during parsing phase!"
        info = "Best match parse branch:  " <> (T.intercalate " -> " . init $ xs)
        err = last xs
      in T.init $ T.unlines [header, "", info, err]

printTypeCheckError :: [Text] -> Text
printTypeCheckError [] = mempty
printTypeCheckError errors =
    let header = "Error occurred during type checking phase!"
      in T.init $ T.unlines $ header: "": errors

printCoreError = id

compilerMain :: Options -> Either Text Text
compilerMain (Options path content lexDump parserDump typeCheckDump noStaticEvaluation coreLangDump emitSSM v) = do
    tokens <- tokenize path content
    let source = T.lines . decodeUtf8 . B.toStrict $ content
    let state = ParserState 0 tokens path source
    if lexDump then
        Right . T.pack . show $ tokens
    else do
        ast <- case runParser pAST state of
            [] -> Left "Internal parser error: Parser did not return any results"
            xs | null (rights xs) -> Left . printParserError . errMsg . fromJust $ maximumOf (folded._Left) xs
               | otherwise -> Right . fst . head $ rights xs

        if parserDump then
            Right . ASTPP.toCode 0 $ ast
        else do
            let tcState = TypeCheckState 0 path source
            initTCT <- Right . reorderTct . ast2tct $ ast
            let typeCheck = detectDuplicateFunctionNames initTCT >> 
                            globalVarConstantCheck initTCT >> 
                            typeCheckTCT initTCT  >>=
                            (if noStaticEvaluation then pure else pure . staticlyEvaluate) >>= 
                            (\r -> returnPathCheck r $> r)
            tct <- case runStateT typeCheck tcState of
                Left err -> Left . printTypeCheckError $ err
                Right (tct, _) -> Right tct

            if typeCheckDump then
                Right . TCTPP.toCode 0 $ tct
            else do
                let clState = CoreState (Some1 HNil) (Some1 HNil) [] 1 1
                Some2 core <- evalStateT (tctToCoreLang tct) clState
                if coreLangDump then do
                    Right $ showCL 0 core
                else
                    if emitSSM then do
                        ssm <- produceSSM core
                        Right $ T.unlines ssm
                    else
                        Left "Not implemented"

