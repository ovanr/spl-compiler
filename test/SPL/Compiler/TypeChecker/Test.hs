{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module SPL.Compiler.TypeChecker.Test (htf_thisModulesTests) where

import Test.Framework
import Control.Monad
import Data.Default
import Data.Text (Text)
import System.Random (mkStdGen)
import Control.Monad.Random
import qualified Data.Set as S
import qualified Data.Map as M

import SPL.Compiler.Common.Testable
import SPL.Compiler.TypeChecker.Testable
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.TypeCheck
import SPL.Compiler.TypeChecker.Unify
import SPL.Compiler.TypeChecker.TypeProperty

type TypeCheckTest a = ((Context, a, TCTType), Maybe Subst)

-- Shorthand operator to create a type check test
infixl 1 ~=
(~=) :: (Context, a, TCTType) -> [(Text, TCTType)] -> TypeCheckTest a 
input ~= subst = (input, Just . Subst $ M.fromList subst)

failure :: (Context, a, TCTType) -> TypeCheckTest a
failure input = (input, Nothing)

var :: Text -> TCTType
var name = TCTUniversalType def (S.singleton name) (TCTVarType def name)

executeTCTests :: [TypeCheckTest a] -> 
                  (Context -> a -> TCTType -> RandErr Error (a, Subst)) -> 
                  IO ()
executeTCTests tests evaluator =
    forM_ tests $ \((gamma, x, t), expected) -> do
        let gen = mkStdGen 10
        let actual = snd . fst <$> runRandT (evaluator gamma x t) gen
        case expected of
            Just subst -> assertEqual (Right subst) (toTestForm actual)
            Nothing -> print actual >> void (assertLeft actual)

-- typeCheckExpr :: Context ->
--                  TCTExpr ->
--                  TCTType ->
--                  RandErr Error (TCTExpr, Subst)

-- type TypeCheckTest a = ((Context, a, TCTType), Maybe Subst)

test_type_check_expr = do
    let tests = [
            (mempty, IntExpr def 5, var "sigma") ~= [("sigma", TCTIntType def)],
            (mempty, BoolExpr def True, TCTBoolType def) ~= [],
            (mempty, EmptyListExpr def, var "sigma") ~= [("sigma", forall ["a"] $ TCTListType def (TCTVarType def "a"))],
            
            failure (mempty, CharExpr def 'c', TCTVarType def "a") 
            ]
    executeTCTests tests typeCheckExpr

