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

type TypeCheckTest a = ((TypeEnv, a, TCTType), Maybe (Either TCTType Subst))

-- Shorthand operator to create a type check test
infixl 1 ~=
(~=) :: ([(Text, Scheme)], a, TCTType) -> TCTType -> TypeCheckTest a
(env, a, t) ~= typ = ((TypeEnv . M.fromList $ env, a, t), Just . Left $ typ)

infixl 1 *=
(*=) :: ([(Text, Scheme)], a, TCTType) -> [(Text,TCTType)] -> TypeCheckTest a
(env, a, t) *= subst = ((TypeEnv . M.fromList $ env, a, t), Just . Right . Subst $ M.fromList subst)


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
            Just (Right subst) -> assertEqual (Right subst) (toTestForm actual)
            Just (Left typ) -> 
                case actual of
                    (Right subst) -> assertEqual typ (toTestForm (subst $* t))
                    Left err -> assertFailure $ "expected substitution but got failure: " <> show err
            Nothing -> print actual >> void (assertLeft actual)

test_type_check_expr = do
    let tests = [
            (mempty, toExpr (5 :: Int), var "sigma") *= [("sigma", TCTIntType def)],
            (mempty, toExpr True, TCTBoolType def) *= [],
            (mempty, toExpr 'c', var "sigma") *= [("sigma", toType 'c')],
            (mempty, toExpr ([] :: [Unknown]), var "sigma") 
            *= [("sigma", toType [var "a"])],
            
            -- ('c', []) :: (Char, [?v])
            (mempty, toExpr ('c', [] :: [Unknown]), var "sigma") 
            *= [("'tup10", TCTCharType def), ("'tup21", toType [var "'l2"]), 
                ("sigma", toType ('c', [var "'l2"]))],

            -- -(5 + 8) :: Int
            (mempty, OpExpr def UnMinus (Op2Expr def (toExpr (5 :: Int)) Plus (toExpr (2 :: Int))), var "sigma")
            ~= TCTIntType def,

            -- 'c' : [] :: [Char]
            (mempty, Op2Expr def (toExpr 'c') Cons (toExpr ([] :: [Char])), var "sigma")
            ~= TCTListType def (TCTCharType def),

            -- x.hd :: v? 
            -- (, FieldSelectExpr (TCTFieldSelector def "v" ,var "sigma")
            -- ~= var "v",

            -- !('c' : []) :: ?v = Fail
            failure (mempty, OpExpr def UnNeg (Op2Expr def (toExpr 'c') Cons (toExpr ([] :: [Char]))), var "sigma"),

            -- 'c' : 'd' :: ?v = Fail
            failure (mempty, Op2Expr def (toExpr 'c') Cons (toExpr 'd'), var "sigma"),

            -- [] :: Int = Fail
            failure (mempty, EmptyListExpr def, TCTIntType def),

            -- 'c' + 'd' :: ?v = Fail
            failure (mempty, Op2Expr def (toExpr 'c') Plus (toExpr 'd'), var "sigma")
            ]

    executeTCTests tests typeCheckExpr

