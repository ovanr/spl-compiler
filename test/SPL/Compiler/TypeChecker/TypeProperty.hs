{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.TypeChecker.TypeProperty where

import Test.Framework
import SPL.Compiler.TypeChecker.Type
import Control.Applicative (liftA2)
import Data.Text (Text)

instance Arbitrary Type where
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
            intGen = return IntType
            boolGen = return BoolType
            charGen = return CharType
            varGen = oneof $ return . VarType <$> ["a", "b", "c", "d"]
            tupleGen = liftA2 TupleType arbitrary arbitrary
            funGen = liftA2 FunType arbitrary arbitrary
            listGen = ListType <$> arbitrary

instance Arbitrary Text where
    arbitrary =  oneof $ return <$> ["a", "b", "c", "d"]

instance Arbitrary Subst where
    arbitrary = Subst <$> arbitrary
