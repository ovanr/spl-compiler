{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# LANGUAGE TypeOperators #-}

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
import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import SPL.Compiler.SemanticAnalysis.TypeProperty
import SPL.Compiler.CodeGen.IRLang (type (-->))

type UnifyTest = ((CoreType, CoreType), Maybe Subst)

-- Shorthand operator to create a unify test
infixl 1 ~*
(~*) :: (CoreType, CoreType) -> [(TypeVar, CoreType)] -> UnifyTest 
types ~* subst = (types, Just . Subst $ M.fromList subst)

failure :: (CoreType, CoreType) -> UnifyTest
failure types = (types, Nothing)

executeUnifyTests :: [UnifyTest] -> IO ()
executeUnifyTests tests =
    forM_ tests $ \((t1,t2), expected) -> do
        let st = TypeCheckState 0 mempty mempty mempty mempty mempty mempty
        let actual = (_getSubst.snd) <$> runStateT (unify t1 t2) st
        case expected of
            Just subst -> assertEqual (Right subst) (toTestForm (minimizeSubst <$> actual)) 
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
            let test = (typ @('[TVar "a"] --> ([TVar "b"], Int)), typ @('[TVar "a"] --> ([Int], Int))) ~* [("b", typ @Int)]
            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_2 = do
            -- U( a -> [c], b -> a ) = [ a |-> [c], b |-> [c] ]
            let test = (typ @('[TVar "a"] --> [TVar "c"]), typ @('[TVar "b"] --> TVar "a"))
                        ~* [("a", typ @[TVar "c"]), ("b", typ @[TVar "c"])]
            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_3 = do
            -- U( (Int, a) -> b, c -> (Int -> Bool) ) = [ c |-> (Int, a), b |-> (Int -> Bool)]
            let test = (typ @('[(Int, TVar "a")] --> TVar "b"), typ @('[TVar "c"] --> ('[Int] --> Bool)))
                        ~* [("c", typ @(Int, TVar "a")), ("b", typ @('[Int] --> Bool))]

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_4 = do
            -- U( a -> a, c -> d ) = [ a |-> d, c |-> d ]
            let test = (typ @('[TVar "a"] --> TVar "a"), typ @('[TVar "c"] --> TVar "d"))
                        ~* [("a", typ @(TVar "d")), ("c", typ @(TVar "d"))]

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_5 = do
            -- U( (b, b) -> c, d -> (d -> d) ) = [d |-> (b,b), c |-> ((b,b) -> (b,b))]
            let test = (typ @('[(TVar "b", TVar "b")] --> TVar "c"), typ @('[TVar "d"] --> ('[TVar "d"] --> TVar "d")))
                    ~* [("d", typ @(TVar "b", TVar "b")), ("c", typ @('[(TVar "b", TVar "b")] --> (TVar "b", TVar "b")))]

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_6 = do
            -- U( a -> ([b], Int), a -> ([Int], Int) ) = [ b |-> Int ]
            let test = (typ @('[TVar "a"] --> ([TVar "b"], Int)), typ @('[TVar "a"] --> ([Int], Int))) ~* [("b", typ @Int)]

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_7 = do
            -- U( a, (b, a) ) = fail
            let test = failure (typ @(TVar "a"), typ @(TVar "b", TVar "a"))

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_8 = do
            -- U( a -> b -> b -> c, a -> d -> d) = fail
            let test = failure (typ @('[TVar "a", TVar "b", TVar "b"] --> TVar "c"), typ @('[TVar "a", TVar "d"] --> TVar "d")) 

            executeUnifyTests [test]
            executeSubstTests [test]

test_unify_9 = do
            -- U( (a -> Int) -> a, (Bool -> Int) -> Int ) = fail
            let test = failure (typ @('[ '[TVar "a"] --> Int] --> TVar "a"), typ @('[ '[ Bool] --> Int] --> Int))

            executeUnifyTests [test]
            executeSubstTests [test]


prop_substitution_law = 
    withQCArgs (\a -> a{maxSuccess = 100, chatty = True}) 
        (\s2 s1 t -> (s2 <> s1 $* (t :: CoreType)) == (s2 $* s1 $* t))
