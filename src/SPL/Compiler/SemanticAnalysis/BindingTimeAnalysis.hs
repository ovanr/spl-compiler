{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis (
    duplicateDefError,
    detectDuplicateFunctionNames
    ) where

import Control.Monad.State
import Control.Monad.Except
import qualified Data.List as L
import Data.List ((\\))

import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TCTEntityLocation
import SPL.Compiler.Common.Error

type SomeErrorStateMonad s m = (MonadState s m, MonadError Error m, ContainsSource s)

duplicateDefError :: SomeErrorStateMonad s m => TCTIdentifier -> m ()
duplicateDefError id@(TCTIdentifier _ idName) = do
    let header = [
            "Redefinition of identifier '" <> idName <> "' not allowed."
            ]
    typeLocTrace <- definition ("'" <> idName <> "' has been declared here:") id
    throwError $ header <> typeLocTrace

detectDuplicateFunctionNames :: SomeErrorStateMonad s m => TCT -> m ()
detectDuplicateFunctionNames (TCT _ funDecls) = do
    let funDecls' = map (\f@(TCTFunDecl _ (TCTIdentifier _ idName) _ _ _ _) -> (idName, f)) (concat funDecls)
        duplicateFuncs = funDecls' \\ L.nubBy (\(i1,_) (i2,_) -> i1 == i2) funDecls'

    mapM_ (\(_, TCTFunDecl _ id _ _ _ _) -> duplicateDefError id) duplicateFuncs
