{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.SemanticAnalysis.SemanticAnalysis where

import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Trans
import qualified Data.Text as T
import Data.Text.IO as TIO
import Data.Text (Text)
import System.IO
import Control.Lens

import SPL.Compiler.Parser.AST (AST)
import SPL.Compiler.SemanticAnalysis.TCT(TCT(..), Error, TypeCheckState(..), getWarnings)
import SPL.Compiler.SemanticAnalysis.TreeTransformer (ast2tct)
import SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis (detectDuplicateFunctionNames)
import SPL.Compiler.SemanticAnalysis.ConstantGlobalVar (globalVarConstantCheck)
import SPL.Compiler.SemanticAnalysis.CallGraphAnalysis (reorderTct)
import SPL.Compiler.SemanticAnalysis.TypeCheck (typeCheckTCT)
import SPL.Compiler.SemanticAnalysis.ReturnPathCheck (returnPathCheck)
import SPL.Compiler.SemanticAnalysis.StaticEvaluation (staticlyEvaluate) 
import Data.Functor (($>))

printTypeCheckError :: [Text] -> Text
printTypeCheckError [] = mempty
printTypeCheckError errors =
    let header = "Error occurred during type checking phase!"
      in T.init $ T.unlines $ header: "": errors

printTypeCheckWarnings :: [Text] -> IO ()
printTypeCheckWarnings [] = mempty
printTypeCheckWarnings warnings =
    let lines = T.init $ T.unlines $ map ("Warning: " <>) warnings
    in TIO.hPutStrLn stderr lines

performSemanticAnalysis :: Bool -> AST -> FilePath -> [Text] -> (ExceptT Text IO) TCT
performSemanticAnalysis noStaticEvaluation ast path source = do
    let tcState = TypeCheckState 0 mempty mempty mempty mempty path source
    let initTCT = reorderTct . ast2tct $ ast
    let typeCheck = detectDuplicateFunctionNames initTCT >> 
                    globalVarConstantCheck initTCT >> 
                    typeCheckTCT initTCT  >>=
                    (if noStaticEvaluation then pure else pure . staticlyEvaluate) >>= 
                    (\r -> returnPathCheck r $> r)
    case runStateT typeCheck tcState of
        Left err -> ExceptT . pure . Left . printTypeCheckError $ err
        Right (tct, st) -> liftIO (printTypeCheckWarnings $ st ^. getWarnings) >> pure tct
