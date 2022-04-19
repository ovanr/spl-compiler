{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module SPL.Compiler.SemanticAnalysis.TCT
    (TCT(..),
     TypeVar,
     Error,
     TypeEnv(..),
     Scheme(..),
     Subst(..),
     TCMonad,
     tcError,
     TypeCheckState(..),
     tvCounter,
     sourcePath,
     sourceCode,
     DeclType(..),
     Scope(..),
     TCTFunDecl(..),
     TCTVarDecl(..),
     TCTIdentifier(..),
     TCTFunBody(..),
     TCTFunCall(..),
     TCTFieldSelector(..),
     TCTField(..),
     TCTStmt(..),
     TCTExpr(..),
     TCon(..),
     TCTType(..),
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
import Control.Monad.Trans
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Lens

import SPL.Compiler.Common.EntityLocation (EntityLoc(..))
import SPL.Compiler.Common.Error
import SPL.Compiler.Parser.AST (OpUnary(..), OpBin(..))

type Error = [Text]
type TypeVar = Text

data Scope = Local Text | Arg | Global deriving (Show, Eq, Ord)

data TypeCheckState =
    TypeCheckState {
        _tvCounter :: Integer,
        _sourcePath :: FilePath,
        _sourceCode :: [Text]
    }

instance ContainsSource TypeCheckState where
    getFilePath = _sourcePath
    getSource = _sourceCode

type TCMonad a = StateT TypeCheckState (Either Error) a

tcError :: Error -> TCMonad a
tcError = lift . Left

makeLenses 'TypeCheckState

data TCT = TCT [TCTVarDecl] [[TCTFunDecl]] deriving (Eq)

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

data TCTFunCall = TCTFunCall EntityLoc TCTIdentifier TCTType [TCTExpr]
    deriving (Eq, Show)

data TCTFieldSelector = TCTFieldSelector EntityLoc TCTIdentifier [TCTField]
    deriving (Eq, Show)

data TCTField = Hd EntityLoc | Tl EntityLoc | Fst EntityLoc | Snd EntityLoc
    deriving (Show)

instance Eq TCTField where
    (Hd _) == (Hd _) = True
    (Tl _) == (Tl _) = True
    (Fst _) == (Fst _) = True
    (Snd _) == (Snd _) = True
    _ == _ = False

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

data TCon =
        TEq TCTType
    |   TOrd TCTType
    |   TPrint TCTType

data TCTType =
        TCTIntType EntityLoc (Set TCon)
    |   TCTBoolType EntityLoc (Set TCon)
    |   TCTCharType EntityLoc (Set TCon)
    |   TCTVoidType EntityLoc (Set TCon)
    |   TCTVarType EntityLoc (Set TCon) TypeVar
    |   TCTTupleType EntityLoc (Set TCon) TCTType TCTType
    |   TCTListType EntityLoc (Set TCon) TCTType
    |   TCTFunType EntityLoc (Set TCon) TCTType TCTType

newtype Subst = Subst (Map TypeVar TCTType) deriving (Eq, Show)
data Scheme = Scheme (Set TypeVar) TCTType
data DeclType = Var | Fun | Both deriving (Eq, Ord)
instance Show DeclType where
    show Var = "Variable"
    show Fun = "Function"
    show Both = "Variable or Function"

newtype TypeEnv = TypeEnv (Map (Text,DeclType) (Scope, Scheme)) deriving (Show)

instance Show Scheme where
    show (Scheme tv t) =
        "forall " <> show (T.intercalate " " $ S.elems tv) <> ". " <> show t

instance Semigroup TypeEnv where
    (TypeEnv e1) <> (TypeEnv e2) = TypeEnv $ M.union e2 e1

instance Monoid TypeEnv where
    mempty = TypeEnv mempty
    mappend = (<>)

instance Eq TCTType where
    (==) = alphaEq

alphaEq :: TCTType -> TCTType -> Bool
alphaEq t1 t2 = evalState (alphaEq' t1 t2) []
    where
        alphaEq' :: TCTType ->
                    TCTType ->
                    State [(TypeVar, TypeVar)] Bool
        alphaEq' (TCTIntType _ _) (TCTIntType _ _) = return True
        alphaEq' (TCTBoolType _ _) (TCTBoolType _ _) = return True
        alphaEq' (TCTCharType _ _) (TCTCharType _ _) = return True
        alphaEq' (TCTVoidType _ _) (TCTVoidType _ _) = return True
        alphaEq' (TCTVarType _ _ a) (TCTVarType _ _ b) = do
            pairs <- get
            if (a,b) `elem` pairs then
                return True
            else
                if not (a `elem` (fst <$> pairs) || b `elem` (snd <$> pairs)) then do
                    put ((a,b) : pairs)
                    return True
                else
                    return False

        alphaEq' (TCTListType _ _ a) (TCTListType _ _ b) = a `alphaEq'` b
        alphaEq' (TCTTupleType _ _ a1 b1) (TCTTupleType _ _ a2 b2) = do
            r1 <- a1 `alphaEq'` a2
            r2 <- b1 `alphaEq'` b2
            return $ r1 && r2
        alphaEq' (TCTFunType _ _ a1 b1) (TCTFunType _ _ a2 b2) = do
            r1 <- a1 `alphaEq'` a2
            r2 <- b1 `alphaEq'` b2
            return $ r1 && r2
        alphaEq' _ _ = return False

instance Show TCTType where
    show (TCTIntType _ _) = "Int"
    show (TCTBoolType _ _) = "Bool"
    show (TCTCharType _ _) = "Char"
    show (TCTVoidType _ _) = "Void"
    show (TCTVarType _ _ a) = T.unpack a
    show (TCTListType _ _ a) = "[" <> show a <> "]"
    show (TCTTupleType _ _ a b) = "(" <> show a <> "," <> show b <> ")"
    show (TCTFunType _ _ a b) =
        case a of
            TCTFunType {} -> "(" <> show a <> ")" <> " -> " <> show b
            _ -> show a <> " -> " <> show b
