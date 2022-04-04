{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.TypeChecker.TypeProperty where

import Test.Framework
import Data.Default
import Control.Applicative (liftA2)
import Data.Text (Text)

import SPL.Compiler.TypeChecker.Testable
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.Unify

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
            intGen = return (TCTIntType def)
            boolGen = return (TCTBoolType def)
            charGen = return (TCTCharType def)
            varGen = oneof $ return . TCTVarType def <$> ["a", "b", "c", "d"]
            tupleGen = liftA2 (TCTTupleType def) arbitrary arbitrary
            funGen = liftA2 (TCTFunType def []) arbitrary arbitrary
            listGen = TCTListType def <$> arbitrary

instance Arbitrary Text where
    arbitrary =  oneof $ return <$> ["a", "b", "c", "d"]

instance Arbitrary Subst where
    arbitrary = Subst <$> arbitrary
