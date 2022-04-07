{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

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

initGammaTest :: TypeEnv
initGammaTest = TypeEnv . M.fromList $ 
    [
     ("hd", forall ["a"] $ typ @([Var "a"] -> Var "a")),
     ("tl", forall ["a"] $ typ @([Var "a"] -> [Var "a"])),
     ("fst", forall ["a","b"] $ typ @((Var "a", Var "b") -> Var "a")),
     ("snd", forall ["a","b"] $ typ @((Var "a", Var "b") -> Var "b"))
    ]

executeTCTests :: [TypeCheckTest a] ->
                  (TypeEnv -> a -> TCTType -> TCMonad (a, Subst)) ->
                  IO ()
executeTCTests tests evaluator =
    forM_ tests $ \((gamma, x, t), expected) -> do
        let st = TypeCheckState 0
        let actual = snd.fst <$> runStateT (evaluator (initGammaTest <> gamma) x t) st
        case expected of
            Just (Right subst) -> assertEqual (Right subst) (toTestForm actual)
            Just (Left typ) -> 
                case actual of
                    (Right subst) -> assertEqual typ (toTestForm (subst $* t))
                    Left err -> assertFailure $ "expected substitution but got failure: " <> show err
            Nothing -> print actual >> void (assertLeft actual)

test_type_check_expr = do
    let tests = [
            -- 5 :: σ = σ |-> Int
            (mempty, iexpr 5, typ @(Var "sigma")) *= [("sigma", typ @Int)],

            -- True :: σ = σ |-> Bool
            (mempty, expr True, typ @Bool) *= [],

            -- 'c' :: σ = σ |-> Char
            (mempty, expr 'c', typ @(Var "sigma")) *= [("sigma", typ @Char)],

            -- [] :: σ = σ |-> [?a]
            (mempty, emptyList, typ @(Var "sigma")) 
            *= [("sigma", typ @[Var "a"])],
            
            -- ('c', []) :: σ = σ |-> (Char, [?'l2]), ...
            (mempty, expr ('c', emptyList) , typ @(Var "sigma")) 
            *= [("'tup10", typ @Char), ("'tup21", typ @[Var "'l2"]), 
                ("sigma", typ @(Char, [Var "'l2"]))],

            -- -(5 + 8) :: Int
            (mempty, op1 UnMinus (op2 (iexpr 5) Plus (iexpr 2)), typ @(Var "sigma"))
            ~= typ @Int,

            -- 'c' : [] :: [Char]
            (mempty, op2 'c' Cons emptyList, typ @(Var "sigma"))
            ~= typ @[Char],

            -- x.hd :: v? 
            ([("x", forall [] $ typ @[Var "v?"])], 
             expr (fd "x" [Hd def]), typ @(Var "sigma"))
            ~= typ @(Var "v?"),

            -- x :: [Int] |- x.hd : x :: [Int] = 
            ([("x", forall [] (typ @[Int]))],
             op2 (fd "x" [Hd def]) Cons (fd "x" []), 
             typ @(Var "sigma"))
            ~= typ @[Int],

            -- x :: [Int] |- x.hd : x :: [Int] = 
            ([("x", forall ["a"] (typ @[Int]))],
             op2 (fd "x" [Hd def]) Cons (fd "x" []),
             typ @(Var "sigma"))
            ~= typ @[Int],

            -- id :: a -> a |- (id 'c') : [] :: [Char] 
            ([("id", forall ["a"] $ typ @(Var "a" -> Var "a"))],
             op2 (fun1 "id" 'c') Cons emptyList, 
             typ @(Var "sigma"))
            ~= typ @[Char],

            -- !('c' : []) :: ?v = Fail
            failure (mempty, op1 UnNeg (op2 'c' Cons emptyList), typ @(Var "sigma")),

            -- 'c' : 'd' :: ?v = Fail
            failure (mempty, op2 'c' Cons 'd', typ @(Var "sigma")),

            -- [] :: Int = Fail
            failure (mempty, emptyList, typ @Int),

            -- 'c' + 'd' :: ?v = Fail
            failure (mempty, op2 'c' Plus 'd', typ @(Var "sigma"))
            ]

    executeTCTests tests typeCheckExpr

