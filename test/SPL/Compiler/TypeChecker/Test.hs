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
var = TCTVarType def

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
--                  RandErr Error (TCTExpr, Subst)

-- type TypeCheckTest a = ((Context, a, TCTType), Maybe Subst)

test_type_check_expr = do
    let tests = [
            (mempty, IntExpr def 5, var "sigma") ~= [("sigma", TCTIntType def)],
            (mempty, BoolExpr def True, TCTBoolType def) ~= [],
            (mempty, CharExpr def 'c', var "sigma") ~= [("sigma", TCTCharType def)],
            (mempty, EmptyListExpr def, var "sigma") 
            ~= [("sigma", TCTListType def (TCTVarType def "a"))]
            ]
    executeTCTests tests typeCheckExpr

