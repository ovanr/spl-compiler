
module SPL.Compiler.SemanticAnalysis.TypeCheck.TCon where

import SPL.Compiler.Common.Error
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Text as T

import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TCTEntityLocation

instance Show TCon where
    show (TEq t) = "Equality " <> show t  
    show (TOrd t) = "Ordered " <> show t  
    show (TPrint t) = "Printable " <> show t  

instance Eq TCon where
    (TEq t1) == (TEq t2) = t1 `strictTypeEq` t2
    (TOrd t1) == (TOrd t2) = t1 `strictTypeEq` t2
    (TPrint t1) == (TPrint t2) = t1 `strictTypeEq` t2
    _ == _ = False

strictTypeEq (TCTIntType _) (TCTIntType _) = True
strictTypeEq (TCTBoolType _) (TCTBoolType _) = True
strictTypeEq (TCTCharType _) (TCTCharType _) = True
strictTypeEq (TCTVoidType _) (TCTVoidType _) = True
strictTypeEq (TCTVarType _ a) (TCTVarType _ b) = a == b 
strictTypeEq (TCTListType _ a) (TCTListType _ b) = a `strictTypeEq` b
strictTypeEq (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = 
    a1 `strictTypeEq` a2 && b1 `strictTypeEq` b2
strictTypeEq (TCTFunType _ c1 a1 b1) (TCTFunType _ c2 a2 b2) =
    c1 == c2 && a1 `strictTypeEq` a2 && b1 `strictTypeEq` b2
strictTypeEq _ _ = False

instance Ord TCon where
    (TEq t1) `compare` (TEq t2) = strictTypeOrd t1 t2
    (TOrd t1) `compare` (TOrd t2) = strictTypeOrd t1 t2
    (TPrint t1) `compare` (TPrint t2) = strictTypeOrd t1 t2
    TEq{} `compare` _ = GT
    TOrd{} `compare` TPrint{} = GT
    TOrd{} `compare` TEq{} = LT
    TPrint{} `compare` _ = LT

strictTypeOrd TCTVoidType{} TCTVoidType{} = EQ
strictTypeOrd TCTVoidType{} _ = LT
strictTypeOrd TCTBoolType{} TCTBoolType{} = EQ
strictTypeOrd TCTBoolType{} TCTVoidType{} = GT
strictTypeOrd TCTBoolType{} _ = LT
strictTypeOrd TCTCharType{} TCTCharType{} = EQ
strictTypeOrd TCTCharType{} TCTVoidType{}  = GT
strictTypeOrd TCTCharType{} TCTBoolType{}  = GT
strictTypeOrd TCTCharType{} _ = LT
strictTypeOrd TCTIntType{} TCTIntType{} = EQ
strictTypeOrd TCTIntType{} TCTVoidType{} = GT
strictTypeOrd TCTIntType{} TCTBoolType{} = GT
strictTypeOrd TCTIntType{} TCTCharType{} = GT
strictTypeOrd TCTIntType{} _ = LT
strictTypeOrd (TCTVarType _ a) (TCTVarType _ b) = a `compare` b 
strictTypeOrd TCTVarType{} TCTListType{} = LT
strictTypeOrd TCTVarType{} TCTTupleType{} = LT
strictTypeOrd TCTVarType{} TCTFunType{} = LT
strictTypeOrd TCTVarType{} _ = GT
strictTypeOrd (TCTListType _ a) (TCTListType _ b) = a `strictTypeOrd` b
strictTypeOrd TCTListType{} TCTTupleType{} = LT
strictTypeOrd TCTListType{} TCTFunType{} = LT
strictTypeOrd TCTListType{} _ = GT
strictTypeOrd (TCTFunType _ c1 a1 b1) (TCTFunType _ c2 a2 b2) =
    case c1 `compare` c2 of
        EQ -> case a1 `strictTypeOrd` a2 of
                    EQ -> b1 `strictTypeOrd` b2
                    x -> x
        y -> y
strictTypeOrd TCTFunType{} TCTTupleType{} = LT
strictTypeOrd TCTFunType{} _ = GT
strictTypeOrd (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) =
    case a1 `strictTypeOrd` a2 of
        EQ -> b1 `strictTypeOrd` b2
        x -> x
strictTypeOrd TCTTupleType{} _ = GT

getTypeCon :: TCTType -> Set TCon
getTypeCon (TCTFunType _ tc t1 t2) = tc <> getTypeCon t1 <> getTypeCon t2
getTypeCon (TCTTupleType _ t1 t2) = getTypeCon t1 <> getTypeCon t2
getTypeCon (TCTListType _ t) = getTypeCon t
getTypeCon _ = mempty

updateTCon :: Set TCon -> TCTType -> TCTType
updateTCon tcon (TCTFunType l _ t1 t2) = TCTFunType l tcon t1 t2
updateTCon _ t = t

validateTCon :: Set TCon -> TCMonad ()
validateTCon = validateTCon' . S.toList
    where
        validateTCon' [] = return ()
        validateTCon' (t@(TEq TCTFunType{}):_) = mkError t >>= tcError
        validateTCon' (TEq _:xs) = validateTCon' xs
        validateTCon' (TOrd TCTIntType{}:xs) = validateTCon' xs
        validateTCon' (TOrd TCTCharType{}:xs) = validateTCon' xs
        validateTCon' (TOrd TCTVarType{}:xs) = validateTCon' xs
        validateTCon' (t@(TOrd _):_) = mkError t >>= tcError
        validateTCon' (t@(TPrint TCTFunType{}):_) = mkError t >>= tcError
        validateTCon' ((TPrint _):xs) = validateTCon' xs
        mkError tcon = do
            let header = T.pack $ "Unable to find an instance for " <> show tcon
            err <- definition (T.pack $ "'" <>
                               show tcon <>
                               "' instance has been inferred for the type: ") tcon
            return $ header : err

