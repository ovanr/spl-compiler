{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module SPL.Compiler.TypeChecker.Test (htf_SPL_Compiler_TypeChecker_Test_thisModulesTests) where

import Test.Framework
import Control.Monad
import Data.Default
import Data.Text (Text)
import System.Random (mkStdGen)
import Control.Monad.State
import qualified Data.Set as S
import qualified Data.Map as M

import SPL.Compiler.Common.Testable
import SPL.Compiler.TypeChecker.Testable
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.TypeCheck
import SPL.Compiler.TypeChecker.Unify
import SPL.Compiler.TypeChecker.TypeProperty

type TypeCheckTest a = ((TypeEnv, a, TCTType), Maybe Subst)

-- Shorthand operator to create a type check test
infixl 1 ~=
(~=) :: ([(Text, Scheme)], a, TCTType) -> [(Text, TCTType)] -> TypeCheckTest a
(env, a, t) ~= subst = ((TypeEnv . M.fromList $ env, a, t), Just . Subst $ M.fromList subst)

failure :: ([(Text, Scheme)], a, TCTType) -> TypeCheckTest a
failure (env, a, t) = ((TypeEnv . M.fromList $ env, a, t), Nothing)

forall :: [Text] -> TCTType -> Scheme
forall vars = Scheme (S.fromList vars)

var :: Text -> TCTType
var = toType

executeTCTests :: [TypeCheckTest a] ->
                  (TypeEnv -> a -> TCTType -> TCMonad (a, Subst)) ->
                  IO ()
executeTCTests tests evaluator =
    forM_ tests $ \((gamma, x, t), expected) -> do
        let st = TypeCheckState 0
        let actual = snd.fst <$> runStateT (evaluator gamma x t) st
        case expected of
            Just subst -> assertEqual (Right subst) (toTestForm actual)
            Nothing -> print actual >> void (assertLeft actual)

-- typeCheckExpr :: Context ->
--                  TCTExpr ->
--                  TCTType ->
--                  TCMonad (TCTExpr, Subst)
test_type_check_expr = do
    let tests = [
            (mempty, toExpr (5 :: Int), var "sigma") ~= [("sigma", TCTIntType def)],
            (mempty, toExpr True, TCTBoolType def) ~= [],
            (mempty, toExpr 'c', var "sigma") ~= [("sigma", toType 'c')],
            (mempty, toExpr ([] :: [Unknown]), var "sigma") 
            ~= [("sigma", toType [var "a"])],
            (mempty, toExpr ('c', [] :: [Unknown]), var "sigma") 
            ~= [("t1", TCTCharType def), ("t2", toType [var "v"]), 
                ("sigma", toType ('c', [var "v"]))],
            failure (mempty, EmptyListExpr def, TCTIntType def)
            ]
    executeTCTests tests typeCheckExpr

