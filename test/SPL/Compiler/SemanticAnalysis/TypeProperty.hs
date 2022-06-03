{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.SemanticAnalysis.TypeProperty where

import Test.Framework
import Data.Default
import Control.Applicative (liftA2)
import qualified Data.Map as M
import Data.Text (Text)

import SPL.Compiler.SemanticAnalysis.Testable
import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.Unify

instance Arbitrary CoreType where
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
            intGen = return (CoreIntType def)
            boolGen = return (CoreBoolType def)
            charGen = return (CoreCharType def)
            varGen = oneof $ return . CoreVarType def <$> ["a", "b", "c", "d"]
            tupleGen = liftA2 (CoreTupleType def) arbitrary arbitrary
            funGen = liftA2 (CoreFunType def) arbitrary arbitrary
            listGen = CoreListType def <$> arbitrary

instance Arbitrary Text where
    arbitrary = oneof $ return <$> ["a1", "b1", "c1", "d1"]

instance Arbitrary Subst where
    arbitrary = Subst <$> arbitrary
