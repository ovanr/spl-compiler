{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module SPL.Compiler.TypeChecker.TypeCheck where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Bifunctor
import Control.Monad.Random

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.Unify

newtype TCError e = TCError { msg :: e }

type RandErr e a = RandT StdGen (Either e) a

type Context = Map Text TCTType

tcFail e = lift (Left e)

freshVar :: MonadRandom m => EntityLoc -> m TCTType
freshVar loc = do
    prefix <- T.singleton <$> getRandomR ('a', 'z')
    suffix <- T.pack . show <$> getRandomR (10000 :: Int, 99999)
    let name = prefix <> suffix
    return $ TCTUniversalType loc (S.singleton name) (TCTVarType loc name) 

-- typeCheckVar :: Context ->
--                 TCTVarDecl ->
--                 RandErr (TCError [Text]) (TCTVarDecl, Subst)
-- typeCheckVar gamma (TCTVarDecl loc t (TCTIdentifier l i) e) = do
--     -- tau <- if 
--     (e', eSubst) <- typeCheckExpr gamma e tau
--     let tau' = substApply eSubst tau
--     tSubst <- lift (getMGTInstance t tau')
--     let subst = tSubst <> eSubst
--     return (TCTVarDecl loc t (TCTIdentifier l i) e', subst)

-- IntExpr EntityLoc Integer
-- CharExpr EntityLoc Char
-- BoolExpr EntityLoc Bool
-- EmptyListExpr EntityLoc
-- OpExpr EntityLoc OpUnary TCTExpr
-- TupExpr EntityLoc TCTExpr TCTExpr
-- FieldSelectExpr TCTFieldSelector
-- FunCallExpr TCTFunCall
-- Op2Expr EntityLoc TCTExpr OpBin TCTExpr  

-- data TCTFunCall = TCTFunCall EntityLoc TCTIdentifier [TCTExpr]
--     deriving (Eq, Show)

typeCheckExpr :: Context ->
                 TCTExpr ->
                 TCTType ->
                 RandErr (TCError [Text]) (TCTExpr, Subst)
typeCheckExpr _ e@(IntExpr loc _) tau = do
    let expectedType = TCTIntType loc
    subst <- lift . first (TCError . pure) $ unify tau expectedType
    return (e, subst)
typeCheckExpr _ e@(CharExpr loc _) tau = do
    let expectedType = TCTCharType loc
    subst <- lift . first (TCError . pure) $ unify tau expectedType
    return (e, subst)
typeCheckExpr _ e@(BoolExpr loc _) tau = do
    let expectedType = TCTBoolType loc
    subst <- lift . first (TCError . pure) $ unify tau expectedType
    return (e, subst)
typeCheckExpr _ e@(EmptyListExpr loc) tau = do
    expectedType <- freshVar loc
    subst <- lift . first (TCError . pure) $ unify tau expectedType
    return (e, subst)
typeCheckExpr gamma e@(TupExpr loc e1 e2) tau = do
    alpha1 <- freshVar (getLoc e1)
    (_, e1Subst) <- typeCheckExpr gamma e1 alpha1
    alpha2 <- freshVar (getLoc e2)
    (_, e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 alpha2
    let eSubst = e2Subst <> e1Subst
    let expectedType = eSubst $* TCTTupleType loc alpha1 alpha2
    subst <- lift . first (TCError . pure) $ unify (eSubst $* tau) expectedType
    return (e, subst <> eSubst)
typeCheckExpr gamma e@(OpExpr loc UnNeg e1) tau = do
    (_, e1Subst) <- typeCheckExpr gamma e1 (TCTBoolType loc)
    let expectedType = TCTBoolType loc
    subst <- lift . first (TCError . pure) $ unify tau expectedType
    return (e, subst <> e1Subst)
typeCheckExpr gamma e@(OpExpr loc UnMinus e1) tau = do
    (_, e1Subst) <- typeCheckExpr gamma e1 (TCTIntType loc)
    let expectedType = TCTIntType loc
    subst <- lift . first (TCError . pure) $ unify tau expectedType
    return (e, subst <> e1Subst)
typeCheckExpr gamma e@(Op2Expr loc e1 op e2) tau =
    case op of
        Plus -> handleIntOp
        Minus -> handleIntOp 
        Mul -> handleIntOp 
        Div -> handleIntOp 
        Mod -> handleIntOp
        Pow -> handleIntOp 
        LogAnd -> handleBoolOp
        LogOr -> handleBoolOp 
        Cons -> handleConsOp 
        _ -> undefined

    where
        handleIntOp = do
            (e1', e1Subst) <- typeCheckExpr gamma e1 (TCTIntType $ getLoc e1)
            (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 (TCTIntType $ getLoc e2)
            let eSubst = e2Subst <> e1Subst
            let expectedType = TCTIntType loc
            subst <- lift . first (TCError . pure) $ unify (eSubst $* tau) expectedType
            return (Op2Expr loc e1' op e2', subst <> eSubst)

        handleBoolOp = do
            (e1', e1Subst) <- typeCheckExpr gamma e1 (TCTBoolType $ getLoc e1)
            (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 (TCTBoolType $ getLoc e2)
            let eSubst = e2Subst <> e1Subst
            let expectedType = TCTBoolType loc
            subst <- lift . first (TCError . pure) $ unify (eSubst $* tau) expectedType
            return (Op2Expr loc e1' op e2', subst <> eSubst)

        handleConsOp = do
            alpha <- freshVar (getLoc e1)
            (e1', e1Subst) <- typeCheckExpr gamma e1 alpha
            (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 
                                            (TCTListType (getLoc e2) (e1Subst $* alpha))
            let eSubst = e2Subst <> e1Subst
            let expectedType = eSubst $* TCTListType (getLoc e) alpha
            subst <- lift . first (TCError . pure) $ unify (eSubst $* tau) expectedType
            return (Op2Expr loc e1' op e2', subst <> eSubst)

        -- | Equal 
        -- | Less 
        -- | Greater 
        -- | LessEq 
        -- | GreaterEq 
        -- | Nequal 
typeCheckExpr _ _ _ = undefined

