{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module SPL.Compiler.SemanticAnalysis.Testable where

import GHC.TypeLits
import Data.Proxy

import SPL.Compiler.CodeGen.CoreLang

class ToCoreType a where
    toCoreType :: Proxy a -> CoreType a

instance ToCoreType Int where
    toCoreType _ = CoreIntType

instance ToCoreType Bool where
    toCoreType _ = CoreBoolType

instance ToCoreType Char where
    toCoreType _ = CoreCharType

instance ToCoreType a => ToCoreType (Ptr [Ptr a]) where
    toCoreType _ = CoreListType (CorePtrType (toCoreType (Proxy @a)))

instance (ToCoreType a, ToCoreType b) => ToCoreType (Ptr (Ptr a, Ptr b)) where
    toCoreType _ = CoreTupleType (CorePtrType $ toCoreType (Proxy @a)) (CorePtrType $ toCoreType (Proxy @b))

-- instance (ToCoreType a, ToCoreType b) => ToCoreType (Ptr ((->) a b)) where
--     toCoreType _ = TCTFunType def mempty (toCoreType (Proxy @a)) (toCoreType (Proxy @b))

data TVar a = TVar

