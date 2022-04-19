{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.SemanticAnalysis.TypeProperty where

import Test.Framework
import Data.Default
import Control.Applicative (liftA2)
import Data.Text (Text)

import SPL.Compiler.SemanticAnalysis.Testable
import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify

instance Arbitrary TCTType where
    arbitrary = frequency
        [
            (2, varGen),
            (2, intGen),
            (2, boolGen),
            (2, charGen),
            (3, funGen),
            (2, listGen),
            (2, tupleGen)
        ]

       where
            intGen = return (TCTIntType def mempty)
            boolGen = return (TCTBoolType def mempty)
            charGen = return (TCTCharType def mempty)
            varGen = oneof $ return . TCTVarType def mempty <$> ["a", "b", "c", "d"]
            tupleGen = liftA2 (TCTTupleType def mempty) arbitrary arbitrary
            funGen = liftA2 (TCTFunType def mempty) arbitrary arbitrary
            listGen = TCTListType def mempty <$> arbitrary

instance Arbitrary Text where
    arbitrary =  oneof $ return <$> ["a", "b", "c", "d"]

instance Arbitrary Subst where
    arbitrary = Subst <$> arbitrary
