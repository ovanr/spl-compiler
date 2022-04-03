{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module SPL.Compiler.TypeChecker.Test (htf_thisModulesTests) where

import Test.Framework
import SPL.Compiler.TypeChecker.Type
import Control.Monad
import qualified Data.Map as M

type UnifyTest = ((Type, Type), Maybe Subst)

-- Shorthand operator to create a unify test
infixl 1 ~*
(~*) :: (Type, Type) -> [(TypeVar, Type)] -> UnifyTest 
types ~* subst = (types, Just . Subst $ M.fromList subst)

failure :: (Type, Type) -> UnifyTest
failure types = (types, Nothing)

executeUnifyTests :: [UnifyTest] -> IO ()
executeUnifyTests tests =
    forM_ tests $ \((t1,t2), expected) -> do
        let actual = unify t1 t2
        case expected of
            Just subst -> assertEqual (Right subst) actual 
            Nothing -> print actual >> void (assertLeft actual)

test_unify = do
    let tests = [
            -- U( a -> ([b], Int), a -> ([Int], Int) ) = [ b |-> Int ]
            (FunType (VarType "a") (TupleType (ListType (VarType "b")) IntType),
             FunType (VarType "a") (TupleType (ListType IntType) IntType))
            ~* [("b", IntType)],

            -- U( a -> [c], b -> a ) = [ a |-> [c], b |-> [c] ]
            (FunType (VarType "a") (ListType (VarType "c")),
             FunType (VarType "b") (VarType "a"))
            ~* [("a", ListType (VarType "c")), ("b", ListType (VarType "c"))],

            -- U( (Int, a) -> b, c -> (Int -> Bool) ) = [ c |-> (Int, a), b |-> (Int -> Bool)]
            (FunType (TupleType IntType (VarType "a")) (VarType "b"), 
             FunType (VarType "c") (FunType IntType BoolType))
            ~* [("c", TupleType IntType (VarType "a")), ("b", FunType IntType BoolType)],

            -- U( a -> a, c -> d ) = [ a |-> d, c |-> d ]
            (FunType (VarType "a") (VarType "a"), FunType (VarType "c") (VarType "d"))
            ~* [("a", VarType "d"), ("c", VarType "d")],

            -- U( (b, b) -> c, d -> (d -> d) ) = [d |-> (b,b), c |-> ((b,b) -> (b,b))]
            (FunType (TupleType (VarType "b") (VarType "b")) (VarType "c"),
             FunType (VarType "d") (FunType (VarType "d") (VarType "d")))
            ~* [("d", TupleType (VarType "b") (VarType "b")), 
                ("c", FunType (TupleType (VarType "b") (VarType "b")) (TupleType (VarType "b") (VarType "b")))],

            -- U( a, (b, a) ) = fail
            failure (VarType "a", TupleType (VarType "b") (VarType "a")),

            -- U( a -> b -> b -> c, a -> d -> d) = fail
            failure (FunType (VarType "a") (FunType (VarType "b") (FunType (VarType "b") (VarType "c"))),
                     FunType (VarType "a") (FunType (VarType "d") (VarType "d"))),

            -- U( (a -> Int) -> a, (Bool -> Int) -> Int ) = fail
            failure (FunType (FunType (VarType "a") IntType) (VarType "a"), FunType (FunType BoolType IntType) IntType)
            ]
    executeUnifyTests tests
