{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Redundant bracket" #-}

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
import SPL.Compiler.TypeChecker.Env (initGamma)
import SPL.Compiler.TypeChecker.TypeCheck
import SPL.Compiler.TypeChecker.Unify
import SPL.Compiler.TypeChecker.TypeProperty

type TypeCheckTest a = ((a, TCTType), Maybe (Either TCTType Subst))
type TypeCheckTestEnv a = ((TypeEnv, a, TCTType), Maybe (Either TCTType Subst))

forall :: [Text] -> TCTType -> Scheme
forall vars = Scheme (S.fromList vars)

-- Shorthand operators to create a type check tests

infixl 2 ~=
(~=) :: (a, TCTType) -> TCTType -> TypeCheckTest a
(a, t) ~= typ = ((a, t), Just . Left $ typ)

infixl 2 ~\=
(~\=) :: a -> TCTType -> TypeCheckTest a
a ~\= t = ((a, t), Nothing)

infixl 2 *=
(*=) :: (a, TCTType) -> [(Text,TCTType)] -> TypeCheckTest a
(a, t) *= subst = ((a, t), Just . Right . Subst $ M.fromList subst)

infixl 2 =:
(=:) :: (Text, TCTType) -> (TCTExpr, TCTType) -> TypeCheckTest TCTVarDecl
(=:) (id, t) (e, rt) = 
    ((TCTVarDecl def t (TCTIdentifier def id) e, t), Just $ Left rt)

infixl 2 =\:
(=\:) :: (Text, TCTType) -> TCTExpr -> TypeCheckTest TCTVarDecl
(=\:) (id, t) e  = 
    ((TCTVarDecl def t (TCTIdentifier def id) e, t), Nothing)

infixl 1 |= 
(|=) :: [(Text, Scheme)] -> TypeCheckTest a -> TypeCheckTestEnv a
(|=) env ((a, t), r) = ((TypeEnv . M.fromList $ env, a, t), r)


executeTCTests :: [TypeCheckTestEnv a] ->
                  (TypeEnv -> a -> TCTType -> TCMonad (a, Subst)) ->
                  IO ()
executeTCTests tests evaluator =
    forM_ tests $ \((gamma, x, t), expected) -> do
        let st = TypeCheckState 0
        let actual = snd.fst <$> runStateT (evaluator (initGamma <> gamma) x t) st
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
            [] |= (iexpr 5, typ @(Var "sigma")) *= [("sigma", typ @Int)],

            -- True :: σ = σ |-> Bool
            [] |= (expr True, typ @Bool) *= [],

            -- 'c' :: σ = σ |-> Char
            [] |= (expr 'c', typ @(Var "sigma")) *= [("sigma", typ @Char)],

            -- [] :: σ = σ |-> [?a]
            [] |= (emptyList, typ @(Var "sigma")) 
            *= [("sigma", typ @[Var "a"])],
            
            -- ('c', []) :: σ = σ |-> (Char, [?'l2]), ...
            [] |= (expr ('c', emptyList) , typ @(Var "sigma")) 
            *= [("'tup10", typ @Char), ("'tup21", typ @[Var "'l2"]), 
                ("sigma", typ @(Char, [Var "'l2"]))],

            -- -(5 + 8) :: Int
            [] |= (op1 UnMinus (op2 (iexpr 5) Plus (iexpr 2)), typ @(Var "sigma"))
            ~= typ @Int,

            -- 'c' : [] :: [Char]
            [] |= (op2 'c' Cons emptyList, typ @(Var "sigma"))
            ~= typ @[Char],

            -- x.hd :: v? 
            [("x", forall [] $ typ @[Var "v?"])] |=
             (expr (fd "x" [Hd def]), typ @(Var "sigma"))
            ~= typ @(Var "v?"),

            -- x :: [Int] |- x.hd : x :: [Int] = 
            [("x", forall [] (typ @[Int]))] |=
             (op2 (fd "x" [Hd def]) Cons (fd "x" []), 
             typ @(Var "sigma"))
            ~= typ @[Int],

            -- x :: [Int] |- x.hd : x :: [Int] = 
            [("x", forall ["a"] (typ @[Int]))] |=
             (op2 (fd "x" [Hd def]) Cons (fd "x" []),
             typ @(Var "sigma"))
            ~= typ @[Int],

            -- id :: a -> a |- (id 'c') : [] :: [Char] 
            [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |=
             (op2 (fun1 "id" 'c') Cons emptyList, 
             typ @(Var "sigma"))
            ~= typ @[Char],

            -- const :: a -> b -> a |- const True :: b -> Bool
            [("const", forall ["a", "b"] $ typ @(Var "a" -> Var "b" -> Var "a"))] |=
            (expr $ fun1 "const" True, typ @(Var "sigma"))
            ~= typ @(Var "b" -> Bool),

            -- repl :: Int -> Char -> [Char]  |- hd (repl 3 'c') :: Char
            [("repl", forall [] $ typ @(Int -> Char -> [Char]))] |=
            (expr $ fun1 "hd" (fun2 "repl" (iexpr 3) 'c'),
             typ @(Var "sigma"))
            ~= typ @Char,

            -- const :: a -> b -> a |- hd (const True []) = fail
            [("const", forall ["a","b"] $ typ @(Var "a" -> Var "b" -> Var "a"))] |=
            expr (fun1 "hd" $ fun2 "const" True emptyList) ~\= typ @(Var "sigma"),

            -- !('c' : []) :: ?v = Fail
            [] |= op1 UnNeg (op2 'c' Cons emptyList) ~\= typ @(Var "sigma"),

            -- 'c' : 'd' :: ?v = Fail
            [] |= op2 'c' Cons 'd' ~\= typ @(Var "sigma"),

            -- [] :: Int = Fail
            [] |= emptyList ~\= typ @Int,

            -- 'c' + 'd' :: ?v = Fail
            [] |= op2 'c' Plus 'd' ~\= typ @(Var "sigma")
            ]

    executeTCTests tests typeCheckExpr

test_type_check_var_decl = do
    let tests = 
            [
                -- Int x = 5
                [] |= ("x", typ @Int) =: (iexpr 5, typ @Int),

                -- y :: Bool |= Bool x = y
                [("y", forall [] $ typ @Bool)] |= ("x", typ @Bool) =: (expr $ fd "y" [], typ @Bool),

                -- [a] x = []
                [] |= ("x", typ @[Var "a"]) =: (emptyList, typ @[Var "b"]),

                -- -- [a] x = []
                -- [] |= ("x", typ @(Bool, [Var "a"])) =: (expr (False, emptyList), typ @(Bool, [Int])),

                -- a x = 5 :: fail
                [] |= ("x", typ @(Var "a")) =\: iexpr 5 
            ]

    executeTCTests tests (\e v _ -> typeCheckVarDecl e v)
