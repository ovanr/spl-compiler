{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module SPL.Compiler.TypeChecker.TypeCheck where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Data.Either.Extra (maybeToEither)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Bifunctor
import Data.Foldable
import Control.Monad.Random

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.Unify

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


typeCheckExpr :: Context ->
                 TCTExpr ->
                 TCTType ->
                 RandErr Error (TCTExpr, Subst)
typeCheckExpr _ e@(IntExpr loc _) tau = do
    let expectedType = TCTIntType loc
    subst <- lift $ unify tau expectedType
    return (e, subst)
typeCheckExpr _ e@(CharExpr loc _) tau = do
    let expectedType = TCTCharType loc
    subst <- lift $ unify tau expectedType
    return (e, subst)
typeCheckExpr _ e@(BoolExpr loc _) tau = do
    let expectedType = TCTBoolType loc
    subst <- lift $ unify tau expectedType
    return (e, subst)
typeCheckExpr _ e@(EmptyListExpr loc) tau = do   
    expectedType <- TCTListType loc <$> freshVar loc
    subst <- lift $ unify tau expectedType
    return (e, subst)
typeCheckExpr gamma e@(FunCallExpr f) tau = do
    (f', fSubst) <- typeCheckFunCall gamma f tau
    return (FunCallExpr f', fSubst)
typeCheckExpr gamma e@(TupExpr loc e1 e2) tau = do
    alpha1 <- freshVar (getLoc e1)
    (e1', e1Subst) <- typeCheckExpr gamma e1 alpha1
    alpha2 <- freshVar (getLoc e2)
    (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 alpha2
    let eSubst = e2Subst <> e1Subst
    let expectedType = eSubst $* TCTTupleType loc alpha1 alpha2
    tauSubst <- lift $ unify (eSubst $* tau) expectedType
    return (TupExpr loc e1' e2', tauSubst <> eSubst)
typeCheckExpr gamma e@(OpExpr loc UnNeg e1) tau = do
    (e1', e1Subst) <- typeCheckExpr gamma e1 (TCTBoolType loc)
    let expectedType = TCTBoolType loc
    tauSubst <- lift $ unify tau expectedType
    return (OpExpr loc UnNeg e1', tauSubst <> e1Subst)
typeCheckExpr gamma e@(OpExpr loc UnMinus e1) tau = do
    (e1', e1Subst) <- typeCheckExpr gamma e1 (TCTIntType loc)
    let expectedType = TCTIntType loc
    tauSubst <- lift $ unify tau expectedType
    return (OpExpr loc UnMinus e1', tauSubst <> e1Subst)
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
            tauSubst <- lift $ unify (eSubst $* tau) expectedType
            return (Op2Expr loc e1' op e2', tauSubst <> eSubst)

        handleBoolOp = do
            (e1', e1Subst) <- typeCheckExpr gamma e1 (TCTBoolType $ getLoc e1)
            (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 (TCTBoolType $ getLoc e2)
            let eSubst = e2Subst <> e1Subst
            let expectedType = TCTBoolType loc
            tauSubst <- lift $ unify (eSubst $* tau) expectedType
            return (Op2Expr loc e1' op e2', tauSubst <> eSubst)

        handleConsOp = do
            alpha <- freshVar (getLoc e1)
            (e1', e1Subst) <- typeCheckExpr gamma e1 alpha
            (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 
                                            (TCTListType (getLoc e2) (e1Subst $* alpha))
            let eSubst = e2Subst <> e1Subst
            let expectedType = eSubst $* TCTListType (getLoc e) alpha
            tauSubst <- lift $ unify (eSubst $* tau) expectedType
            return (Op2Expr loc e1' op e2', tauSubst <> eSubst)

        -- | Equal 
        -- | Less 
        -- | Greater 
        -- | LessEq 
        -- | GreaterEq 
        -- | Nequal 
typeCheckExpr _ _ _ = undefined

-- forall c. c ->> forall c. forall a. a -> Void ->> forall c a. a -> Void ->> forall a. a -> Void
-- forall a. a -> Void
-- [ c |-> forall a. a -> Void ] 

typeCheckVar :: Context ->
                TCTIdentifier ->
                TCTType ->
                RandErr Error (TCTIdentifier, Subst)
typeCheckVar gamma id@(TCTIdentifier l idName) tau = do
    idType <- lift . maybeToEither ["Variable not found " <> idName] $ M.lookup idName gamma
    subst <- lift $ unify idType tau
    return (id, subst)

-- assume gamma contains = hd :: forall a. [a] -> a, tl :: forall a. [a] -> [a], fst :: forall a b. (a,b) -> a
--                         snd :: forall a b. (a,b) -> b
typeCheckFieldSelector :: Context -> TCTFieldSelector -> TCTType -> RandErr Error (TCTFieldSelector, Subst)
typeCheckFieldSelector gamma fldslct@(TCTFieldSelector loc id []) t = do
    (id', subst) <- typeCheckVar gamma id t
    return (fldslct, subst)
    
typeCheckFieldSelector gamma fldslct@(TCTFieldSelector loc id fields) t = do
    (_, subst) <- typeCheckVar gamma (toVar $ last fields) t
    (_, subst') <- typeCheckFieldSelector (subst $* gamma) (TCTFieldSelector loc id (init fields)) (subst $* t)
    return (fldslct, subst' <> subst)
    
    where
        toVar :: TCTField -> TCTIdentifier
        toVar (Hd loc) = TCTIdentifier loc "hd"
        toVar (Tl loc) = TCTIdentifier loc "tl"
        toVar (Fst loc) = TCTIdentifier loc "fst"
        toVar (Snd loc) = TCTIdentifier loc "snd"



-- data TCTFunCall = TCTFunCall EntityLoc TCTIdentifier [TCTExpr]

typeCheckFunCall :: Context -> TCTFunCall -> TCTType -> RandErr Error (TCTFunCall, Subst)
typeCheckFunCall gamma (TCTFunCall locF id@(TCTIdentifier locI _) args) tau = do
    (args', funType, argsSubst) <- foldrM typeCheckArgs ([], tau, mempty) args
    (id', idSubst) <- typeCheckVar gamma id funType

    return (TCTFunCall locF id' args', idSubst <> argsSubst)

    where
        typeCheckArgs :: TCTExpr -> 
                         ([TCTExpr], TCTType, Subst) -> 
                         RandT StdGen (Either Error) ([TCTExpr], TCTType, Subst)
        typeCheckArgs arg (exprs, funType, prevSubst) = do
            -- generate freshVar for each arg
            -- get a subst for each arg and compose them sequentially
            alpha <- freshVar (getLoc arg)
            (arg', argSubst) <- typeCheckExpr (prevSubst $* gamma) arg alpha
            let subst = argSubst <> prevSubst
            return (arg' : exprs, 
                    TCTFunType (getLoc arg) [] (subst $* alpha) funType, 
                    subst)

typeCheckStmt :: Context ->
                 TCTStmt ->
                 TCTType -> 
                 RandErr Error (TCTStmt, Subst)
typeCheckStmt gamma stmt@(IfElseStmt loc cond thenStmts elseStmts) t = do
    (_, condSubst) <- typeCheckExpr gamma cond (TCTBoolType $ getLoc cond)
    (_, thenSubst) <- typeCheckStmtList (condSubst $* gamma) thenStmts (condSubst $* t)
    let combSubst = thenSubst <> condSubst
    (_, elseSubst) <- typeCheckStmtList (combSubst $* gamma) elseStmts (combSubst $* t)
    return (stmt, combSubst <> elseSubst)

typeCheckStmt gamma stmt@(WhileStmt loc cond bodyStmts) t = do
    (_, condSubst) <- typeCheckExpr gamma cond (TCTBoolType $ getLoc cond)
    (_, bodySubst) <- typeCheckStmtList (condSubst $* gamma) bodyStmts (condSubst $* t)
    return (stmt, bodySubst <> condSubst)

typeCheckStmt gamma stmt@(AssignStmt loc field expr) t = do
    alpha1 <- freshVar (getLoc field)
    (_, fieldSubst) <- typeCheckFieldSelector gamma field alpha1
    alpha2 <- freshVar (getLoc expr)
    (_, exprSubst) <- typeCheckExpr (fieldSubst $* gamma) expr alpha2
    let combSubst = exprSubst <> fieldSubst
    subst <- lift $ unify (combSubst $* alpha1) (combSubst $* alpha2) 
    return (stmt, subst <> combSubst)

typeCheckStmt gamma stmt@(ReturnStmt loc Nothing) t = do
    subst <- lift $ unify t (TCTVoidType loc)
    return (stmt, mempty)

typeCheckStmt gamma stmt@(ReturnStmt loc (Just expr)) t = do
    alpha <- freshVar loc
    (_, exprSubst) <- typeCheckExpr gamma expr alpha
    subst <- lift $ unify (exprSubst $* alpha) (exprSubst $* t) 
    return (stmt, subst <> exprSubst)

typeCheckStmt gamma stmt@(FunCallStmt loc funCall) t = undefined
    



typeCheckStmtList :: Context ->
                     [TCTStmt] ->
                     TCTType ->
                     RandErr Error ([TCTStmt], Subst)
typeCheckStmtList _ [] _ = return ([], mempty)
typeCheckStmtList gamma (st:sts) t = do
    (_, substSt)  <- typeCheckStmt gamma st t
    (_, substSts) <- typeCheckStmtList (substSt $* gamma) sts (substSt $* t)
    return (st:sts, substSt <> substSts)
