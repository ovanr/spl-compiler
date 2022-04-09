{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant bracket" #-}

module SPL.Compiler.TypeChecker.TestUnify (htf_thisModulesTests) where

import Test.Framework
import Control.Monad
import Data.Default
import Data.Text (Text)
import Control.Monad.State
import qualified Data.Set as S
import qualified Data.Map as M

import SPL.Compiler.Common.Testable
import SPL.Compiler.TypeChecker.Testable
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.Unify
import SPL.Compiler.TypeChecker.TypeProperty

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

test_unify = do
    let tests = [
            -- U( a -> ([b], Int), a -> ([Int], Int) ) = [ b |-> Int ]
            (TCTFunType def mempty (TCTVarType def "a") (TCTTupleType def (TCTListType def (TCTVarType def "b")) (TCTIntType def)),
             TCTFunType def mempty (TCTVarType def "a") (TCTTupleType def (TCTListType def (TCTIntType def)) (TCTIntType def)))
            ~* [("b", TCTIntType def)],

            -- U( a -> [c], b -> a ) = [ a |-> [c], b |-> [c] ]
            (TCTFunType def mempty (TCTVarType def "a") (TCTListType def (TCTVarType def "c")),
             TCTFunType def mempty (TCTVarType def "b") (TCTVarType def "a"))
            ~* [("a", TCTListType def (TCTVarType def "c")), ("b", TCTListType def (TCTVarType def "c"))],

            -- U( (Int, a) -> b, c -> (Int -> Bool) ) = [ c |-> (Int, a), b |-> (Int -> Bool)]
            (TCTFunType def mempty (TCTTupleType def (TCTIntType def) (TCTVarType def "a")) (TCTVarType def "b"), 
             TCTFunType def mempty (TCTVarType def "c") (TCTFunType def mempty (TCTIntType def) (TCTBoolType def)))
            ~* [("c", TCTTupleType def (TCTIntType def) (TCTVarType def "a")), 
                ("b", TCTFunType def mempty (TCTIntType def) (TCTBoolType def))],

            -- U( a -> a, c -> d ) = [ a |-> d, c |-> d ]
            (TCTFunType def mempty (TCTVarType def "a") (TCTVarType def "a"), 
             TCTFunType def mempty (TCTVarType def "c") (TCTVarType def "d"))
            ~* [("a", TCTVarType def "d"), ("c", TCTVarType def "d")],

            -- U( (b, b) -> c, d -> (d -> d) ) = [d |-> (b,b), c |-> ((b,b) -> (b,b))]
            (TCTFunType def mempty (TCTTupleType def (TCTVarType def "b") (TCTVarType def "b")) (TCTVarType def "c"),
             TCTFunType def mempty (TCTVarType def "d") (TCTFunType def mempty (TCTVarType def "d") (TCTVarType def "d")))
            ~* [("d", TCTTupleType def (TCTVarType def "b") (TCTVarType def "b")), 
                ("c", TCTFunType def mempty (TCTTupleType def (TCTVarType def "b") (TCTVarType def "b")) 
                                        (TCTTupleType def (TCTVarType def "b") (TCTVarType def "b")))],

            -- U( a -> ([b], Int), a -> ([Int], Int) ) = [ b |-> Int ]
            (TCTFunType def mempty (TCTVarType def "a") (TCTTupleType def (TCTListType def (TCTVarType def "b")) (TCTIntType def)),
             TCTFunType def mempty (TCTVarType def "a") (TCTTupleType def (TCTListType def (TCTIntType def)) (TCTIntType def)))
            ~* [("b", TCTIntType def)], 

            -- U( a, (b, a) ) = fail
            failure (TCTVarType def "a", TCTTupleType def (TCTVarType def "b") (TCTVarType def "a")),

            -- U( a -> b -> b -> c, a -> d -> d) = fail
            failure (TCTFunType def mempty (TCTVarType def "a") (TCTFunType def mempty (TCTVarType def "b") 
                                       (TCTFunType def mempty (TCTVarType def "b") (TCTVarType def "c"))),
                     TCTFunType def mempty (TCTVarType def "a") (TCTFunType def mempty (TCTVarType def "d") (TCTVarType def "d"))),

            -- U( (a -> Int) -> a, (Bool -> Int) -> Int ) = fail
            failure (TCTFunType def mempty (TCTFunType def mempty (TCTVarType def "a") (TCTIntType def)) (TCTVarType def "a"), 
                     TCTFunType def mempty (TCTFunType def mempty (TCTBoolType def) (TCTIntType def)) (TCTIntType def))
            ]
    executeUnifyTests tests
    executeSubstTests tests


prop_substitutionLaw = 
    withQCArgs (\a -> a{maxSuccess = 1000}) 
        (\s2 s1 t -> (s2 <> s1 $* (t :: TCTType)) == (s2 $* s1 $* t))
