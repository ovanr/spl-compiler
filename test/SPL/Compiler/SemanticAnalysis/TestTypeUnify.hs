{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant bracket" #-}

module SPL.Compiler.SemanticAnalysis.TestTypeUnify (htf_thisModulesTests) where

import Test.Framework
import Control.Monad
import Data.Default
import Data.Text (Text)
import Control.Monad.State
import qualified Data.Set as S
import qualified Data.Map as M

import SPL.Compiler.Common.Testable
import SPL.Compiler.SemanticAnalysis.Testable
import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import SPL.Compiler.SemanticAnalysis.TypeProperty

type UnifyTest = ((TCTType, TCTType), Maybe Subst)

-- Shorthand operator to create a unify test
infixl 1 ~*
(~*) :: (TCTType, TCTType) -> [(TypeVar, TCTType)] -> UnifyTest 
types ~* subst = (types, Just . Subst $ M.fromList subst)

failure :: (TCTType, TCTType) -> UnifyTest
failure types = (types, Nothing)

executeUnifyTests :: [UnifyTest] -> IO ()
executeUnifyTests tests =
    forM_ tests $ \((t1,t2), expected) -> do
        let st = TypeCheckState 0 mempty mempty
        let actual = fst <$> runStateT (unify t1 t2) st
        case expected of
            Just subst -> assertEqual (Right subst) (toTestForm actual) 
            Nothing -> print actual >> void (assertLeft actual)

executeSubstTests :: [UnifyTest] -> IO ()
executeSubstTests tests =
    forM_ tests $ \((t1,t2), expected) -> do
        let actual = unify t1 t2
        case expected of
            Just subst -> assertEqual (subst $* t1) (subst $* t2) 
            Nothing -> return ()


test_unify_1 = do
            -- U( a -> ([b], Int), a -> ([Int], Int) ) = [ b |-> Int ]
            let test = (typ @(Var "a" -> ([Var "b"], Int)), typ @(Var "a" -> ([Int], Int))) ~* [("b", typ @Int)]
            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_2 = do
            -- U( a -> [c], b -> a ) = [ a |-> [c], b |-> [c] ]
            let test = (typ @(Var "a" -> [Var "c"]), typ @(Var "b" -> Var "a"))
                        ~* [("a", typ @[Var "c"]), ("b", typ @[Var "c"])]
            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_3 = do
            -- U( (Int, a) -> b, c -> (Int -> Bool) ) = [ c |-> (Int, a), b |-> (Int -> Bool)]
            let test = (typ @((Int, Var "a") -> Var "b"), typ @(Var "c" -> Int -> Bool))
                        ~* [("c", typ @(Int, Var "a")), ("b", typ @(Int -> Bool))]

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_4 = do
            -- U( a -> a, c -> d ) = [ a |-> d, c |-> d ]
            let test = (typ @(Var "a" -> Var "a"), typ @(Var "c" -> Var "d"))
                        ~* [("a", typ @(Var "d")), ("c", typ @(Var "d"))]

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_5 = do
            -- U( (b, b) -> c, d -> (d -> d) ) = [d |-> (b,b), c |-> ((b,b) -> (b,b))]
            let test = (typ @((Var "b", Var "b") -> Var "c"), typ @(Var "d" -> Var "d" -> Var "d"))
                    ~* [("d", typ @(Var "b", Var "b")), ("c", typ @((Var "b", Var "b") -> (Var "b", Var "b")))]

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_6 = do
            -- U( a -> ([b], Int), a -> ([Int], Int) ) = [ b |-> Int ]
            let test = (typ @(Var "a" -> ([Var "b"], Int)), typ @(Var "a" -> ([Int], Int))) ~* [("b", typ @Int)]

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_7 = do
            -- U( a, (b, a) ) = fail
            let test = failure (typ @(Var "a"), typ @(Var "b", Var "a"))

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_8 = do
            -- U( a -> b -> b -> c, a -> d -> d) = fail
            let test = failure (typ @(Var "a" -> Var "b" -> Var "b" -> Var "c"), typ @(Var "a" -> Var "d" -> Var "d")) 

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_9 = do
            -- U( (a -> Int) -> a, (Bool -> Int) -> Int ) = fail
            let test = failure (typ @((Var "a" -> Int) -> Var "a"), typ @((Bool -> Int) -> Int))

            executeUnifyTests [test]
            executeSubstTests [test]


prop_substitutionLaw = 
    withQCArgs (\a -> a{maxSuccess = 1000}) 
        (\s2 s1 t -> (s2 <> s1 $* (t :: TCTType)) == (s2 $* s1 $* t))
