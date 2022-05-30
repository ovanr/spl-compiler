{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis (
    duplicateDefError,
    detectDuplicateFunctionNames
    ) where

import Control.Monad.State
import Control.Monad.Except
import Data.Tuple.Extra
import Data.Either
import Data.Graph
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import Data.List ((\\))

import SPL.Compiler.Parser.AST
import SPL.Compiler.Parser.ASTEntityLocation
import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error

type SomeErrorStateMonad s m = (MonadState s m, MonadError Error m, ContainsSource s)

duplicateDefError :: (SomeErrorStateMonad s m) => ASTIdentifier -> m ()
duplicateDefError (ASTIdentifier l id) = do
    let header = [
            "Redefinition of identifier '" <> id <> "' not allowed."
            ]
    typeLocTrace <- definition ("'" <> id <> "' has been declared here:") l
    throwError $ header <> typeLocTrace

detectDuplicateFunctionNames :: SomeErrorStateMonad s m => AST -> m ()
detectDuplicateFunctionNames ast = do
    let identifiers = decompose ast
        duplicates = identifiers \\ L.nubBy (\(i1,_) (i2,_) -> i1 == i2) identifiers

    mapM_ (duplicateDefError . snd) duplicates

    where
        decompose :: AST -> [(Text, ASTIdentifier)]
        decompose (ASTUnordered leaves) = map (getName &&& getIdentifier) leaves
        decompose (ASTOrdered varDecls funDecls) =
            map ((getName &&& getIdentifier) . Left) varDecls ++
            map ((getName &&& getIdentifier) . Right) (concatMap sccToList funDecls)
        sccToList (AcyclicSCC x) = [x]
        sccToList (CyclicSCC xs) = xs
        getIdentifier (Left (ASTVarDecl _ _ id _)) = id
        getIdentifier (Right (ASTFunDecl _ id _ _ _)) = id
        getName x = let ASTIdentifier _ id = getIdentifier x in id
