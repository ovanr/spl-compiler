{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.SemanticAnalysis.SemanticAnalysis where

import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Trans
import qualified Data.Text as T
import qualified Data.Map as M
import Data.Text.IO as TIO
import Data.Text (Text)
import System.IO
import Control.Lens

import SPL.Compiler.Parser.AST (AST)
import SPL.Compiler.SemanticAnalysis.Core(Core(..), CoreType(..), Error, TypeCheckState(..), getWarnings)
import SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis (detectDuplicateFunctionNames)
import SPL.Compiler.SemanticAnalysis.ConstantGlobalVar (globalVarConstantCheck)
import SPL.Compiler.SemanticAnalysis.ConstantFold (constantFold) 
import SPL.Compiler.SemanticAnalysis.TypeCheck (typeCheckToCore)
import SPL.Compiler.SemanticAnalysis.ReturnPathCheck (returnPathCheck)
import SPL.Compiler.SemanticAnalysis.Overload (resolveOverloading)
import SPL.Compiler.SemanticAnalysis.OverloadLib (TCon(..), TConState(..))
import Data.Functor (($>))

printTypeCheckError :: [Text] -> Text
printTypeCheckError [] = mempty
printTypeCheckError errors =
    let header = "Error occurred during semantic analysis phase."
      in T.init $ T.unlines $ header: "": errors

printTypeCheckWarnings :: [Text] -> IO ()
printTypeCheckWarnings [] = mempty
printTypeCheckWarnings warnings =
    let lines = T.init $ T.unlines $ map ("Warning: " <>) warnings
    in TIO.hPutStrLn stderr lines

resolveOverloading' :: FilePath -> [Text] -> Core -> ExceptT Text IO Core
resolveOverloading' path source core = do
    let printType = ([TPrint mempty "a"], CoreFunType mempty (Just $ CoreVarType mempty "a") (CoreVoidType mempty))
                                          
    let tcState = TConState (M.singleton "print" printType) mempty mempty path source
    case runStateT (resolveOverloading core) tcState of
        Left err -> ExceptT . pure . Left . printTypeCheckError $ err
        Right (core, st) -> pure core

performSemanticAnalysis :: Bool -> AST -> FilePath -> [Text] -> ExceptT Text IO Core
performSemanticAnalysis noOptimization ast path source = do
    let tcState = TypeCheckState 0 0 mempty mempty mempty path source
    let typeCheck = detectDuplicateFunctionNames ast >> 
                    globalVarConstantCheck ast >> 
                    typeCheckToCore ast >>=
                    (if noOptimization then pure else pure . constantFold) >>= 
                    (\r -> returnPathCheck r $> r)
    case runStateT typeCheck tcState of
        Left err -> ExceptT . pure . Left . printTypeCheckError $ err
        Right (core, st) -> do
            liftIO (printTypeCheckWarnings $ st ^. getWarnings)
            resolveOverloading' path source core
