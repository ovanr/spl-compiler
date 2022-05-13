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
     varDeclLoc, 
     varDeclType,
     varDeclId,
     varDeclExpr,
     tcError,
     TypeCheckState(..),
     getTvCounter,
     getSubst,
     getEnv,
     getTcons,
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
     funTcons,
     funBody,
     funCallLoc,
     funCallId,
     funCallType,
     funCallTcons,
     funCallArgs,
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

data Scope = Local | Arg | Global deriving (Show, Eq, Ord)

data DeclType = Var | Fun | Both deriving (Eq, Ord)

newtype Subst = Subst { unSubst :: Map TypeVar TCTType } deriving (Eq, Show)

data Scheme = Scheme (Set TypeVar) [TCon] TCTType

newtype TypeEnv = TypeEnv (Map (Text,DeclType) (Scope, Scheme)) deriving (Show)

data TypeCheckState =
    TypeCheckState {
        _getTvCounter :: Integer,
        _getSubst :: Subst,
        _getEnv :: TypeEnv,
        _getTcons :: [TCon],
        _getWarnings :: [Text],
        _getSourcePath :: FilePath,
        _getSourceCode :: [Text]
    }
    deriving (Show)

instance ContainsSource TypeCheckState where
    getFilePath = _getSourcePath
    getSource = _getSourceCode

type TCMonad a = StateT TypeCheckState (Either Error) a

tcError :: Error -> TCMonad a
tcError = lift . Left

data TCT = TCT [TCTVarDecl] [[TCTFunDecl]] deriving (Eq)

data TCTFunDecl =
    TCTFunDecl {
        _funDeclLoc :: EntityLoc,
        _funId :: TCTIdentifier,
        _funArgs :: [TCTIdentifier],
        _funType :: TCTType,
        _funTcons :: [TCon],
        _funBody :: TCTFunBody
    } deriving (Eq, Show)

data TCTVarDecl = TCTVarDecl {
    _varDeclLoc :: EntityLoc,
    _varDeclType :: TCTType,
    _varDeclId :: TCTIdentifier,
    _varDeclExpr :: TCTExpr
} deriving (Eq, Show)

data TCTIdentifier = TCTIdentifier { _idLoc :: EntityLoc, _idName :: Text }
    deriving (Eq, Show)

data TCTFunBody = TCTFunBody EntityLoc [TCTVarDecl] [TCTStmt]
    deriving (Eq, Show)

data TCTFunCall = 
    TCTFunCall { 
        _funCallLoc :: EntityLoc,
        _funCallId :: TCTIdentifier,
        _funCallType :: TCTType,
        _funCallTcons :: [TCon],
        _funCallArgs :: [TCTExpr]
    } deriving (Eq, Show)

data TCTFieldSelector = TCTFieldSelector EntityLoc TCTIdentifier TCTType [TCTField]
    deriving (Eq, Show)

data TCTField = Hd EntityLoc | Tl EntityLoc | Fst EntityLoc | Snd EntityLoc

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
    |   EmptyListExpr EntityLoc TCTType
    |   TupExpr EntityLoc TCTExpr TCTExpr
    deriving (Eq, Show)

data TCTType =
        TCTIntType EntityLoc
    |   TCTBoolType EntityLoc 
    |   TCTCharType EntityLoc 
    |   TCTVoidType EntityLoc 
    |   TCTVarType EntityLoc TypeVar
    |   TCTTupleType EntityLoc TCTType TCTType
    |   TCTListType EntityLoc TCTType
    |   TCTFunType EntityLoc TCTType TCTType
    
data TCon =
        TEq TCTType
    |   TOrd TCTType
    |   TPrint TCTType

alphaEq :: TCTType -> TCTType -> Bool
alphaEq t1 t2 = evalState (alphaEq' t1 t2) []
    where
        alphaEq' :: TCTType ->
                    TCTType ->
                    State [(TypeVar, TypeVar)] Bool
        alphaEq' (TCTIntType _) (TCTIntType _) = return True
        alphaEq' (TCTBoolType _) (TCTBoolType _) = return True
        alphaEq' (TCTCharType _) (TCTCharType _) = return True
        alphaEq' (TCTVoidType _) (TCTVoidType _) = return True
        alphaEq' (TCTVarType _ a) (TCTVarType _ b) = do
            pairs <- get
            if (a,b) `elem` pairs then
                return True
            else
                if not (a `elem` (fst <$> pairs) || b `elem` (snd <$> pairs)) then do
                    put ((a,b) : pairs)
                    return True
                else
                    return False

        alphaEq' (TCTListType _ a) (TCTListType _ b) = a `alphaEq'` b
        alphaEq' (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = do
            r1 <- a1 `alphaEq'` a2
            r2 <- b1 `alphaEq'` b2
            return $ r1 && r2
        alphaEq' (TCTFunType _ a1 b1) (TCTFunType _ a2 b2) = do
            r1 <- a1 `alphaEq'` a2
            r2 <- b1 `alphaEq'` b2
            return $ r1 && r2
        alphaEq' _ _ = return False

strictTypeEq :: TCTType -> TCTType -> Bool
strictTypeEq TCTIntType{} TCTIntType{} = True
strictTypeEq TCTBoolType{} TCTBoolType{} = True
strictTypeEq TCTCharType{}  TCTCharType{} = True
strictTypeEq TCTVoidType{} TCTVoidType{} = True
strictTypeEq (TCTVarType _ a) (TCTVarType _ b) = a == b 
strictTypeEq (TCTListType _ a) (TCTListType _ b) = a `strictTypeEq` b
strictTypeEq (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = 
    a1 `strictTypeEq` a2 && b1 `strictTypeEq` b2
strictTypeEq (TCTFunType _ a1 b1) (TCTFunType _ a2 b2) =
    a1 `strictTypeEq` a2 && b1 `strictTypeEq` b2
strictTypeEq _ _ = False

instance Eq TCTType where
    (==) = alphaEq

instance Eq TCon where
    (TEq t1) == (TEq t2) = t1 `strictTypeEq` t2
    (TOrd t1) == (TOrd t2) = t1 `strictTypeEq` t2
    (TPrint t1) == (TPrint t2) = t1 `strictTypeEq` t2
    _ == _ = False

instance Eq TCTField where
    (Hd _) == (Hd _) = True
    (Tl _) == (Tl _) = True
    (Fst _) == (Fst _) = True
    (Snd _) == (Snd _) = True
    _ == _ = False

instance Show TCTType where
    show (TCTIntType _) = "Int"
    show (TCTBoolType _) = "Bool"
    show (TCTCharType _) = "Char"
    show (TCTVoidType _) = "Void"
    show (TCTVarType _ a) = T.unpack a
    show (TCTListType _ a) = "[" <> show a <> "]"
    show (TCTTupleType _ a b) = "(" <> show a <> "," <> show b <> ")"
    show (TCTFunType _ a b) =
        case a of
            TCTFunType {} -> "(" <> show a <> ")" <> " -> " <> show b
            _ -> show a <> " -> " <> show b

instance Show TCon where
    show (TEq t) = "Equality " <> show t  
    show (TOrd t) = "Ordered " <> show t  
    show (TPrint t) = "Printable " <> show t  

instance Show DeclType where
    show Var = "Variable"
    show Fun = "Function"
    show Both = "Variable or Function"

instance Show Scheme where
    show (Scheme tv _ t) =
        "forall " <> show (T.intercalate " " $ S.elems tv) <> ". " <> show t

instance Show TCTField where
    show (Hd _) = "hd"
    show (Tl _) = "tl"
    show (Fst _) = "fst"
    show (Snd _) = "snd"

instance Semigroup TypeEnv where
    (TypeEnv e1) <> (TypeEnv e2) = TypeEnv $ M.union e2 e1

instance Monoid TypeEnv where
    mempty = TypeEnv mempty
    mappend = (<>)

makeLenses 'TypeCheckState
makeLenses 'TCTIdentifier
makeLenses 'TCTVarDecl
makeLenses 'TCTFunDecl
makeLenses 'TCTFunCall
