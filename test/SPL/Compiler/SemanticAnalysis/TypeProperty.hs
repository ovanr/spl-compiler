{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.SemanticAnalysis.TypeProperty where

import Test.Framework
import Data.Default
import Control.Applicative (liftA2)
import qualified Data.Map as M
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
            intGen = return (TCTIntType def)
            boolGen = return (TCTBoolType def)
            charGen = return (TCTCharType def)
            varGen = oneof $ return . TCTVarType def <$> ["a", "b", "c", "d"]
            tupleGen = liftA2 (TCTTupleType def) arbitrary arbitrary
            funGen = liftA2 (TCTFunType def) arbitrary arbitrary
            listGen = TCTListType def <$> arbitrary

instance Arbitrary Text where
    arbitrary = oneof $ return <$> ["a1", "b1", "c1", "d1"]

instance Arbitrary Subst where
    arbitrary = Subst <$> arbitrary
