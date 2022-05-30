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
     varDeclLoc,
     varDeclType,
     varDeclId,
     varDeclExpr,
     tcError,
     TypeCheckState(..),
     unTCon,
     areTConSameKind,
     getTvCounter,
     getSubst,
     getEnv,
     getTCons,
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
     isConcreteType,
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
     TCon(..),
     TCon'(..),
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
import Control.Lens

import SPL.Compiler.Common.EntityLocation (EntityLoc(..))
import SPL.Compiler.Common.Error
import SPL.Compiler.Parser.AST (OpUnary(..), OpBin(..), Field(..))

type TypeVar = Text

data Scope = Local | Arg | GlobalVar | GlobalFun deriving (Show, Eq, Ord)

newtype Subst = Subst { unSubst :: Map TypeVar CoreType } deriving (Eq, Show)

data Scheme = Scheme (Set TypeVar) CoreType

newtype TypeEnv = TypeEnv (Map Text (Scope, Scheme)) deriving (Show)

data TypeCheckState =
    TypeCheckState {
        _getTvCounter :: Integer,
        _getSubst :: Subst,
        _getEnv :: TypeEnv,
        _getTCons :: Set TCon, 
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

data Core = Core [CoreVarDecl] [CoreFunDecl] deriving (Eq)

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

data CoreFunBody = CoreFunBody EntityLoc [CoreVarDecl] [CoreStmt]
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
    |   FunIdentifierExpr CoreIdentifier
    |   OpExpr EntityLoc OpUnary CoreExpr
    |   Op2Expr EntityLoc CoreExpr OpBin CoreExpr
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
    |   CoreFunType EntityLoc [TCon] [CoreType] CoreType

data TCon' a =
        TEq a
    |   TOrd a
    |   TPrint a

type TCon = TCon' CoreType

unTCon :: TCon -> CoreType
unTCon (TEq t) = t
unTCon (TOrd t) = t
unTCon (TPrint t) = t

areTConSameKind :: TCon -> TCon -> Bool
areTConSameKind (TEq _) (TEq _) = True
areTConSameKind (TOrd _) (TOrd _) = True
areTConSameKind (TPrint _) (TPrint _) = True
areTConSameKind _ _ = False

isConcreteType :: CoreType -> Bool
isConcreteType CoreVarType{} = False
isConcreteType (CoreTupleType _ t1 t2) =
    isConcreteType t1 && isConcreteType t2
isConcreteType (CoreListType _ t) = isConcreteType t
isConcreteType (CoreFunType _ tcon as r) = 
    all (isConcreteType.unTCon) tcon && all isConcreteType as && isConcreteType r
isConcreteType _ = True

alphaEq :: CoreType -> CoreType -> Bool
alphaEq t1 t2 = evalState (alphaEq' t1 t2) []
    where
        alphaEq' :: CoreType ->
                    CoreType ->
                    State [(TypeVar, TypeVar)] Bool
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
        alphaEq' (CoreFunType _ tcon1 xs r1) (CoreFunType _ tcon2 ys r2) = do
            if length xs == length ys && length tcon1 == length tcon2 then do
                fmap and . sequence $
                    [r1 `alphaEq'` r2,
                    pure . and $ zipWith areTConSameKind tcon1 tcon2,
                    and <$> zipWithM alphaEq' (map unTCon tcon1) (map unTCon tcon2),
                    and <$> zipWithM alphaEq' xs ys]
            else
                return False
        alphaEq' _ _ = return False

strictTypeEq :: CoreType -> CoreType -> Bool
strictTypeEq t1 t2 = hash t1 == hash t2

instance Eq CoreType where
    (==) = alphaEq

instance Eq TCon where
    t1 == t2 = areTConSameKind t1 t2 && unTCon t1 `strictTypeEq` unTCon t2

instance Hashable TCon where
    hashWithSalt seed (TEq t) = hashWithSalt (hashWithSalt seed t) (1 :: Int)
    hashWithSalt seed (TOrd t) = hashWithSalt (hashWithSalt seed t) (2 :: Int)
    hashWithSalt seed (TPrint t) = hashWithSalt (hashWithSalt seed t) (3 :: Int)

instance Hashable CoreType where
    hashWithSalt seed CoreVoidType{} = hashWithSalt seed (1 :: Int)
    hashWithSalt seed CoreBoolType{} = hashWithSalt seed (2 :: Int)
    hashWithSalt seed CoreIntType{} = hashWithSalt seed (3 :: Int)
    hashWithSalt seed CoreCharType{} = hashWithSalt seed (4 :: Int)
    hashWithSalt seed (CoreVarType _ txt) = hashWithSalt (hashWithSalt seed txt) (5 :: Int)
    hashWithSalt seed (CoreTupleType _ t1 t2) = hashWithSalt (hashWithSalt (hashWithSalt seed t1) t2) (6 :: Int)
    hashWithSalt seed (CoreListType _ t1) = hashWithSalt (hashWithSalt seed t1) (7 :: Int)
    hashWithSalt seed (CoreFunType _ tcs as r) = 
        foldl hashWithSalt (hashWithSalt (foldl hashWithSalt seed as) r) tcs

instance Show TCon where
    show (TEq t) = "Equality " <> show t
    show (TOrd t) = "Ordered " <> show t
    show (TPrint t) = "Printable " <> show t

instance {-# OVERLAPS #-} Show [TCon] where
    show [] = ""
    show xs = T.unpack $ " /* (" <> body <> ") */ "
        where
            body = T.intercalate ", " . map (T.pack . show) $ xs

instance Show CoreType where
    show (CoreIntType _) = "Int"
    show (CoreBoolType _) = "Bool"
    show (CoreCharType _) = "Char"
    show (CoreVoidType _) = "Void"
    show (CoreVarType _ a) = T.unpack a
    show (CoreListType _ a) = "[" <> show a <> "]"
    show (CoreTupleType _ a b) = "(" <> show a <> "," <> show b <> ")"
    show (CoreFunType _ _ [] r) = "-> " <> show r
    show (CoreFunType _ cs as r) = "(" <> show cs <> unwords (map show as) <> " -> " <> show r <> ")"

instance Ord TCon where
    compare x y = compare (hash x) (hash y)

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
