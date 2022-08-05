{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}

module SPL.Compiler.SemanticAnalysis.Core
    (Core(..),
     TypeVar,
     Error,
     TypeEnv(..),
     Scheme(..),
     Subst(..),
     TCMonad,
     Offset,
     varDeclLoc,
     varDeclType,
     varDeclId,
     varDeclExpr,
     TypeCheckState(..),
     getTvCounter,
     getLocalVarCounter,
     getSubst,
     getEnv,
     getWarnings,
     getSourcePath,
     getSourceCode,
     strictTypeEq,
     idLoc,
     idName,
     funDeclLoc,
     funId,
     funArgs,
     funType,
     funBody,
     funCallLoc,
     funCallExpr,
     funCallType,
     funCallArgs,
     Scope(..),
     CoreFunDecl(..),
     CoreVarDecl(..),
     CoreIdentifier(..),
     CoreFunBody(..),
     CoreFunCall(..),
     Field(..),
     CoreStmt(..),
     CoreExpr(..),
     CoreType(..),
     OpUnary(..),
     OpBin(..),
     EntityLoc
    )
    where

import Data.Text (Text)
import Data.Set (Set)
import Data.Map (Map)
import Control.Monad.State.Lazy
import Data.Foldable
import Data.Hashable
import Control.Monad.Trans
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Graph
import Control.Lens

import SPL.Compiler.Common.EntityLocation (EntityLoc(..))
import SPL.Compiler.Common.Error
import SPL.Compiler.Parser.AST (OpUnary(..), OpBin(..), Field(..))
import Data.Maybe (fromMaybe)

type TypeVar = Text

data Scope = Local | Arg | GlobalVar | GlobalFun deriving (Show, Eq, Ord)

newtype Subst = Subst { unSubst :: Map TypeVar CoreType } deriving (Eq, Show)

data Scheme = Scheme (Set TypeVar) CoreType

newtype TypeEnv = TypeEnv (Map Text (Scope, Scheme)) deriving (Show)

data TypeCheckState =
    TypeCheckState {
        _getTvCounter :: Integer,
        _getLocalVarCounter :: Integer,
        _getSubst :: Subst,
        _getEnv :: TypeEnv,
        _getWarnings :: [Text],
        _getSourcePath :: FilePath,
        _getSourceCode :: [Text]
    }
    deriving (Show)

instance ContainsSource TypeCheckState where
    getFilePath = _getSourcePath
    getSource = _getSourceCode

type TCMonad a = StateT TypeCheckState (Either Error) a

data Core = Core [CoreVarDecl] [SCC CoreFunDecl] deriving (Eq)

data CoreFunDecl =
    CoreFunDecl {
        _funDeclLoc :: EntityLoc,
        _funId :: CoreIdentifier,
        _funArgs :: [CoreIdentifier],
        _funType :: CoreType,
        _funBody :: CoreFunBody
    } deriving (Eq, Show)

data CoreVarDecl = CoreVarDecl {
    _varDeclLoc :: EntityLoc,
    _varDeclType :: CoreType,
    _varDeclId :: CoreIdentifier,
    _varDeclExpr :: CoreExpr
} deriving (Eq, Show)

data CoreIdentifier = CoreIdentifier { _idLoc :: EntityLoc, _idName :: Text }
    deriving (Eq, Show)

type Offset = Integer
data CoreFunBody = CoreFunBody EntityLoc [CoreStmt]
    deriving (Eq, Show)

data CoreFunCall =
    CoreFunCall {
        _funCallLoc :: EntityLoc,
        _funCallExpr :: CoreExpr,
        _funCallType :: CoreType,
        _funCallArgs :: [CoreExpr]
    } deriving (Eq, Show)

data CoreStmt =
        IfElseStmt EntityLoc CoreExpr [CoreStmt] [CoreStmt]
    |   WhileStmt EntityLoc CoreExpr [CoreStmt]
    |   VarDeclStmt Offset CoreVarDecl
    |   AssignStmt EntityLoc CoreIdentifier CoreType [Field] CoreExpr
    |   FunCallStmt CoreFunCall
    |   ReturnStmt EntityLoc (Maybe CoreExpr)
    deriving (Eq, Show)

data CoreExpr =
        IntExpr EntityLoc Integer
    |   CharExpr EntityLoc Char
    |   BoolExpr EntityLoc Bool
    |   FunCallExpr CoreFunCall
    |   VarIdentifierExpr CoreIdentifier
    |   FunIdentifierExpr CoreType CoreIdentifier
    |   OpExpr EntityLoc OpUnary CoreExpr
    |   Op2Expr EntityLoc CoreExpr CoreType OpBin CoreExpr CoreType
    |   EmptyListExpr EntityLoc CoreType
    |   TupExpr EntityLoc CoreExpr CoreExpr
    deriving (Eq, Show)

data CoreType =
        CoreIntType EntityLoc
    |   CoreBoolType EntityLoc
    |   CoreCharType EntityLoc
    |   CoreVoidType EntityLoc
    |   CoreVarType EntityLoc TypeVar
    |   CoreTupleType EntityLoc CoreType CoreType
    |   CoreListType EntityLoc CoreType
    |   CoreFunType EntityLoc (Maybe CoreType) CoreType

alphaEq :: CoreType -> CoreType -> Bool
alphaEq t1 t2 = evalState (alphaEq' t1 t2) []
    where
        alphaEq' :: CoreType -> CoreType -> State [(TypeVar, TypeVar)] Bool
        alphaEq' (CoreIntType _) (CoreIntType _) = return True
        alphaEq' (CoreBoolType _) (CoreBoolType _) = return True
        alphaEq' (CoreCharType _) (CoreCharType _) = return True
        alphaEq' (CoreVoidType _) (CoreVoidType _) = return True
        alphaEq' (CoreVarType _ a) (CoreVarType _ b) = do
            pairs <- get
            if (a,b) `elem` pairs then
                return True
            else
                if not (a `elem` (fst <$> pairs) || b `elem` (snd <$> pairs)) then do
                    put ((a,b) : pairs)
                    return True
                else
                    return False
        alphaEq' (CoreListType _ a) (CoreListType _ b) = a `alphaEq'` b
        alphaEq' (CoreTupleType _ a1 b1) (CoreTupleType _ a2 b2) = do
            r1 <- a1 `alphaEq'` a2
            r2 <- b1 `alphaEq'` b2
            return $ r1 && r2
        alphaEq' (CoreFunType _ Nothing b1) (CoreFunType _ Nothing b2) = return $ b1 `alphaEq` b2
        alphaEq' (CoreFunType _ (Just a1) b1) (CoreFunType _ (Just a2) b2) = do
            r1 <- a1 `alphaEq'` a2
            r2 <- b1 `alphaEq'` b2
            return $ r1 && r2
        alphaEq' _ _ = return False

strictTypeEq :: CoreType -> CoreType -> Bool
strictTypeEq t1 t2 = hash t1 == hash t2

instance Hashable CoreType where
    hashWithSalt seed CoreVoidType{} = hashWithSalt seed (1 :: Int)
    hashWithSalt seed CoreBoolType{} = hashWithSalt seed (2 :: Int)
    hashWithSalt seed CoreIntType{} = hashWithSalt seed (3 :: Int)
    hashWithSalt seed CoreCharType{} = hashWithSalt seed (4 :: Int)
    hashWithSalt seed (CoreVarType _ txt) = hashWithSalt (hashWithSalt seed txt) (5 :: Int)
    hashWithSalt seed (CoreTupleType _ t1 t2) = hashWithSalt (hashWithSalt (hashWithSalt seed t1) t2) (6 :: Int)
    hashWithSalt seed (CoreListType _ t1) = hashWithSalt (hashWithSalt seed t1) (7 :: Int)
    hashWithSalt seed (CoreFunType _ a b) =
        hashWithSalt (hashWithSalt seed a) b

instance Eq CoreType where
    (==) = alphaEq

instance Show CoreType where
    show t = show' False t
        where
            show' _ (CoreIntType _) = "Int"
            show' _ (CoreBoolType _) = "Bool"
            show' _ (CoreCharType _) = "Char"
            show' _ (CoreVoidType _) = "Void"
            show' _ (CoreVarType _ a) = T.unpack a
            show' _ (CoreListType _ a) = "[" <> show' False a <> "]"
            show' _ (CoreTupleType _ a b) = "(" <> show' False a <> "," <> show' False b <> ")"
            show' False (CoreFunType _ Nothing r) = "-> " <> show' True r
            show' True (CoreFunType _ Nothing r) = "(-> " <> show' True r <> ")"
            show' False (CoreFunType _ (Just a) r) = show' True a <> " -> " <> show' True r
            show' True (CoreFunType _ (Just a) r) = "(" <> show' True a <> " -> " <> show' True r <> ")"

instance Show Scheme where
    show (Scheme tv t) =
        "forall " <> show (T.intercalate " " $ S.elems tv) <> ". " <> show t

instance Semigroup TypeEnv where
    (TypeEnv e1) <> (TypeEnv e2) = TypeEnv $ M.union e2 e1

instance Monoid TypeEnv where
    mempty = TypeEnv mempty
    mappend = (<>)

makeLenses 'TypeCheckState
makeLenses 'CoreIdentifier
makeLenses 'CoreVarDecl
makeLenses 'CoreFunDecl
makeLenses 'CoreFunCall
