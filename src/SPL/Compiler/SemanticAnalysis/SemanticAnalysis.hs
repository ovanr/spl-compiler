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
import SPL.Compiler.SemanticAnalysis.Core(Core(..), Error, TypeCheckState(..), getWarnings)
import SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis (detectDuplicateFunctionNames)
import SPL.Compiler.SemanticAnalysis.ConstantGlobalVar (globalVarConstantCheck)
import SPL.Compiler.SemanticAnalysis.TypeCheck (typeCheckToCore)
import SPL.Compiler.SemanticAnalysis.ReturnPathCheck (returnPathCheck)
import SPL.Compiler.SemanticAnalysis.ConstantFold (constantFold) 
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

performSemanticAnalysis :: Bool -> AST -> FilePath -> [Text] -> (ExceptT Text IO) Core
performSemanticAnalysis noOptimization ast path source = do
    let tcState = TypeCheckState 0 mempty mempty mempty mempty path source
    let typeCheck = detectDuplicateFunctionNames ast >> 
                    globalVarConstantCheck ast >> 
                    typeCheckToCore ast >>=
                    (if noOptimization then pure else pure . constantFold) >>= 
                    (\r -> returnPathCheck r $> r)
    case runStateT typeCheck tcState of
        Left err -> ExceptT . pure . Left . printTypeCheckError $ err
        Right (tct, st) -> liftIO (printTypeCheckWarnings $ st ^. getWarnings) >> pure tct
