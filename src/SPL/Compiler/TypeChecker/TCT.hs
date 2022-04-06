{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.TypeChecker.TCT
    (TCT(..),
     TypeVar,
     TCTLeaf(..),
     TCTFunDecl(..),
     TCTVarDecl(..),
     TCTIdentifier(..),
     TCTFunBody(..),
     TCTFunCall(..),
     TCTFieldSelector(..),
     TCTField(..),
     TCTStmt(..),
     TCTExpr(..),
     TypeConstraints(..),
     TCTType(..),
     OpUnary(..),
     OpBin(..),
     EntityLoc
    )
    where

import Data.Text (Text)
import Data.Set (Set)
import Control.Monad.State.Lazy
import Data.Foldable
import qualified Data.Text as T
import qualified Data.Set as S
import Control.Lens

import SPL.Compiler.Common.EntityLocation (EntityLoc(..))
import SPL.Compiler.Parser.AST (OpUnary(..), OpBin(..))

type TypeVar = Text

newtype TCT = TCT [TCTLeaf]

data TCTLeaf =
        TCTVar TCTVarDecl
    |   TCTFun TCTFunDecl

data TCTFunDecl =
    TCTFunDecl
        EntityLoc
        TCTIdentifier
        [TCTIdentifier]
        TCTType
        TCTFunBody
    deriving (Eq, Show)

data TCTVarDecl = TCTVarDecl EntityLoc TCTType TCTIdentifier TCTExpr
    deriving (Eq, Show)

data TCTIdentifier = TCTIdentifier EntityLoc Text
    deriving (Eq, Show)

data TCTFunBody = TCTFunBody EntityLoc [TCTVarDecl] [TCTStmt]
    deriving (Eq, Show)

data TCTFunCall = TCTFunCall EntityLoc TCTIdentifier [TCTExpr]
    deriving (Eq, Show)

data TCTFieldSelector = TCTFieldSelector EntityLoc TCTIdentifier [TCTField]
    deriving (Eq, Show)

data TCTField = Hd EntityLoc | Tl EntityLoc | Fst EntityLoc | Snd EntityLoc
    deriving (Eq, Show)

data TCTStmt =
        IfElseStmt EntityLoc TCTExpr [TCTStmt] [TCTStmt]
    |   WhileStmt EntityLoc TCTExpr [TCTStmt]
    |   AssignStmt EntityLoc TCTFieldSelector TCTExpr
    |   FunCallStmt EntityLoc TCTFunCall
    |   ReturnStmt EntityLoc (Maybe TCTExpr)
    deriving (Eq, Show)

data TCTExpr =
        IntExpr EntityLoc Integer
    |   CharExpr EntityLoc Char
    |   BoolExpr EntityLoc Bool
    |   FunCallExpr TCTFunCall
    |   FieldSelectExpr TCTFieldSelector
    |   OpExpr EntityLoc OpUnary TCTExpr
    |   Op2Expr EntityLoc TCTExpr OpBin TCTExpr
    |   EmptyListExpr EntityLoc
    |   TupExpr EntityLoc TCTExpr TCTExpr
    deriving (Eq, Show)

data TypeConstraints =
        Eq T.Text
    |   Ord T.Text
    |   Print T.Text
    deriving (Eq, Show)

data TCTType =
        TCTIntType EntityLoc
    |   TCTBoolType EntityLoc
    |   TCTCharType EntityLoc
    |   TCTVoidType EntityLoc
    |   TCTVarType EntityLoc TypeVar
    |   TCTUniversalType EntityLoc (Set TypeVar) TCTType
    |   TCTTupleType EntityLoc TCTType TCTType
    |   TCTListType EntityLoc TCTType
    |   TCTFunType EntityLoc [TypeConstraints] TCTType TCTType

instance Eq TCTType where
    (==) = alphaEq

alphaEq :: TCTType -> TCTType -> Bool
alphaEq t1 t2 = evalState (alphaEq' t1 t2) (mempty, mempty, [])
    where
        alphaEq' :: TCTType ->
                    TCTType ->
                    State (Set TypeVar, Set TypeVar, [(TypeVar, TypeVar)]) Bool
        alphaEq' (TCTIntType _) (TCTIntType _) = return True
        alphaEq' (TCTBoolType _) (TCTBoolType _) = return True
        alphaEq' (TCTCharType _) (TCTCharType _) = return True
        alphaEq' (TCTVoidType _) (TCTVoidType _) = return True
        alphaEq' (TCTVarType _ a) (TCTVarType _ b) = do
            (tv1, tv2, pairs) <- get
            if S.member a tv1 && S.member b tv2 then do
                if (a,b) `elem` pairs then
                    return True
                else
                    if not (a `elem` (fst <$> pairs) || b `elem` (snd <$> pairs)) then do
                        put (tv1, tv2, pairs ++ [(a,b)]) 
                        return True
                    else
                        return False
            else
                if not (S.member a tv1) && not (S.member b tv2) then
                    return $ a == b
                else
                    return False

        alphaEq' (TCTUniversalType _ tv1 t1) (TCTUniversalType _ tv2 t2) =
            if length tv1 /= length tv2 then
                return False
            else do
                (tv1',tv2', pairs) <- get
                put (tv1' <> tv1, tv2' <> tv2, pairs)
                t1 `alphaEq'` t2
        alphaEq' (TCTUniversalType _ tv t1) t2 = do
            let r1 = null tv
            r2 <- t1 `alphaEq'` t2
            return $ r1 && r2
        alphaEq' t1 (TCTUniversalType _ tv t2) = do
            let r1 = null tv
            r2 <- t1 `alphaEq'` t2
            return $ r1 && r2
        alphaEq' (TCTListType _ a) (TCTListType _ b) = a `alphaEq'` b
        alphaEq' (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = do
            r1 <- a1 `alphaEq'` a2
            r2 <- b1 `alphaEq'` b2
            return $ r1 && r2
        alphaEq' (TCTFunType _ c1 a1 b1) (TCTFunType _ c2 a2 b2) = do
            let r1 = c1 == c2
            r2 <- a1 `alphaEq'` a2
            r3 <- b1 `alphaEq'` b2
            return $ r1 && r2 && r3
        alphaEq' _ _ = return False

instance Show TCTType where
    show (TCTIntType _) = "Int"
    show (TCTBoolType _) = "Bool"
    show (TCTCharType _) = "Char"
    show (TCTVoidType _) = "Void"
    show (TCTVarType _ a) = T.unpack a
    show (TCTUniversalType _ tv a) =
        if null tv then
            show a
        else
            "forall " <> T.unpack (T.intercalate " " $ S.toList tv) <> ". " <>
            show a
    show (TCTListType _ a) = "[" <> show a <> "]"
    show (TCTTupleType _ a b) = "(" <> show a <> "," <> show b <> ")"
    show (TCTFunType _ _ a b) =
        case a of
            TCTFunType {} -> "(" <> show a <> ")" <> " -> " <> show b
            _ -> show a <> " -> " <> show b
