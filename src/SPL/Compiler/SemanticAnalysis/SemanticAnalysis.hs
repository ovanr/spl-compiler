{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.SemanticAnalysis.SemanticAnalysis where

import Control.Monad.State
import qualified Data.Text as T
import Data.Text (Text)

import SPL.Compiler.Parser.AST (AST)
import SPL.Compiler.SemanticAnalysis.TCT(TCT(..), Error, TypeCheckState(..))
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

performSemanticAnalysis :: Bool -> AST -> FilePath -> [Text] -> Either Text TCT
performSemanticAnalysis noStaticEvaluation ast path source = do
    let tcState = TypeCheckState 0 mempty mempty mempty path source
    initTCT <- Right . reorderTct . ast2tct $ ast
    let typeCheck = detectDuplicateFunctionNames initTCT >> 
                    globalVarConstantCheck initTCT >> 
                    typeCheckTCT initTCT  >>=
                    (if noStaticEvaluation then pure else pure . staticlyEvaluate) >>= 
                    (\r -> returnPathCheck r $> r)
    case runStateT typeCheck tcState of
        Left err -> Left . printTypeCheckError $ err
        Right (tct, _) -> Right tct
