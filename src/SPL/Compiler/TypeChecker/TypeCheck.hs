{-# LANGUAGE TupleSections #-}
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
import Data.Maybe
import Control.Monad.State
import Control.Lens
import Debug.Trace

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.Env (initGamma)
import SPL.Compiler.TypeChecker.Unify


sanitize :: TCTType -> TCMonad TCTType
sanitize = instantiate . generalise mempty

instantiate :: Scheme -> TCMonad TCTType
instantiate (Scheme tv t) = do
    newNames <- mapM (\v -> (v,) <$> freshVar (fromMaybe (getLoc t) (findLoc v t)) v) $ S.toList tv
    let subst = Subst . M.fromList $ newNames
    return $ subst $* t

    where
        findLoc :: TypeVar -> TCTType -> Maybe EntityLoc
        findLoc v1 (TCTVarType l v2)
            | v1 == v2 = Just l
            | otherwise = Nothing
        findLoc v1 (TCTListType _ t) = findLoc v1 t
        findLoc v1 (TCTTupleType _ t1 t2) = 
            listToMaybe $ catMaybes [findLoc v1 t1, findLoc v1 t2]
        findLoc v1 (TCTFunType _ _ t1 t2) = 
            listToMaybe $ catMaybes [findLoc v1 t1, findLoc v1 t2]
        findLoc _ _ = Nothing

freshVar :: EntityLoc -> Text -> TCMonad TCTType
freshVar loc prefix = do
    suffix <- T.pack . show <$> use tvCounter
    tvCounter += 1
    return $ TCTVarType loc (prefix <> suffix)


isInstanceOf :: TCTType -> Scheme -> TCMonad Subst
isInstanceOf t sch = do
    sanitizedT <- sanitize t
    isInstanceOf' sanitizedT sch

    where
        isInstanceOf' :: TCTType -> Scheme -> TCMonad Subst
        isInstanceOf' (TCTVoidType _) (Scheme _ (TCTVoidType _)) = return mempty
        isInstanceOf' (TCTIntType _)  (Scheme _ (TCTIntType _)) = return mempty
        isInstanceOf' (TCTCharType _) (Scheme _ (TCTCharType _)) = return mempty
        isInstanceOf' (TCTBoolType _) (Scheme _ (TCTBoolType _)) = return mempty
        isInstanceOf' v@(TCTVarType _ t) (Scheme tv v2@(TCTVarType l a))
            | S.member a tv = return . Subst $ M.singleton a (setLoc l v)
            | not (S.member a tv) && a == t = return mempty
            | otherwise = typeMismatchError v2 v

        isInstanceOf' t (Scheme tv v@(TCTVarType l a))
            | S.member a tv = return . Subst $ M.singleton a (setLoc l t)
            | otherwise = typeMismatchError v t

        isInstanceOf' (TCTListType _ t1) (Scheme tv (TCTListType _ t2)) =
           isInstanceOf' t1 (Scheme tv t2)

        isInstanceOf' (TCTTupleType _ a1 b1) (Scheme tv (TCTTupleType _ a2 b2)) = do
            subst1 <- isInstanceOf' a1 (Scheme tv a2)
            subst2 <- isInstanceOf' b1 (Scheme tv $ subst1 $* b2)
            return $ subst2 <> subst1

        isInstanceOf' (TCTFunType _ _ a1 b1) (Scheme tv (TCTFunType _ _ a2 b2)) = do
            subst1 <- isInstanceOf' a1 (Scheme tv a2)
            subst2 <- isInstanceOf' b1 (Scheme tv $ subst1 $* b2)
            return $ subst2 <> subst1

        isInstanceOf' t1 (Scheme _ t2) = typeMismatchError t2 t1

typeCheckExpr :: TypeEnv ->
                 TCTExpr ->
                 TCTType ->
                 TCMonad (TCTExpr, Subst)
typeCheckExpr _ e@(IntExpr loc _) tau = do
    let expectedType = TCTIntType loc
    subst <- unify expectedType tau
    return (e, subst)
typeCheckExpr _ e@(CharExpr loc _) tau = do
    let expectedType = TCTCharType loc
    subst <- unify expectedType tau
    return (e, subst)
typeCheckExpr _ e@(BoolExpr loc _) tau = do
    let expectedType = TCTBoolType loc
    subst <- unify expectedType tau
    return (e, subst)
typeCheckExpr _ e@(EmptyListExpr loc) tau = do
    expectedType <- TCTListType loc <$> freshVar loc "l"
    subst <- unify expectedType tau
    return (e, subst)
typeCheckExpr gamma e@(FunCallExpr f) tau = do
    (f', fSubst) <- typeCheckFunCall gamma f tau
    return (FunCallExpr f', fSubst)
typeCheckExpr gamma e@(FieldSelectExpr fs) tau = do
    (fs', fSubst) <- typeCheckFieldSelector gamma fs tau
    return (FieldSelectExpr fs', fSubst)
typeCheckExpr gamma e@(TupExpr loc e1 e2) tau = do
    alpha1 <- freshVar (getLoc e1) "tup1"
    (e1', e1Subst) <- typeCheckExpr gamma e1 alpha1
    alpha2 <- freshVar (getLoc e2) "tup2"
    (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 alpha2
    let eSubst = e2Subst <> e1Subst
    let expectedType = eSubst $* TCTTupleType loc alpha1 alpha2
    tauSubst <- unify expectedType (eSubst $* tau)
    return (TupExpr loc e1' e2', tauSubst <> eSubst)
typeCheckExpr gamma e@(OpExpr loc UnNeg e1) tau = do
    (e1', e1Subst) <- typeCheckExpr gamma e1 (TCTBoolType loc)
    let expectedType = TCTBoolType loc
    tauSubst <- unify expectedType (e1Subst $* tau)
    return (OpExpr loc UnNeg e1', tauSubst <> e1Subst)
typeCheckExpr gamma e@(OpExpr loc UnMinus e1) tau = do
    (e1', e1Subst) <- typeCheckExpr gamma e1 (TCTIntType loc)
    let expectedType = TCTIntType loc
    tauSubst <- unify expectedType (e1Subst $* tau)
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
            tauSubst <- unify expectedType (eSubst $* tau) 
            return (Op2Expr loc e1' op e2', tauSubst <> eSubst)

        handleBoolOp = do
            (e1', e1Subst) <- typeCheckExpr gamma e1 (TCTBoolType $ getLoc e1)
            (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 (TCTBoolType $ getLoc e2)
            let eSubst = e2Subst <> e1Subst
            let expectedType = TCTBoolType loc
            tauSubst <- unify expectedType (eSubst $* tau)
            return (Op2Expr loc e1' op e2', tauSubst <> eSubst)

        handleConsOp = do
            alpha <- freshVar (getLoc e1) "cons"
            (e1', e1Subst) <- typeCheckExpr gamma e1 alpha
            (e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2
                                            (TCTListType (getLoc e2) (e1Subst $* alpha))
            let eSubst = e2Subst <> e1Subst
            let expectedType = eSubst $* TCTListType (getLoc e) alpha
            tauSubst <- unify expectedType (eSubst $* tau) 
            return (Op2Expr loc e1' op e2', tauSubst <> eSubst)

        -- | Equal 
        -- | Less 
        -- | Greater 
        -- | LessEq 
        -- | GreaterEq 
        -- | Nequal 

variableNotFoundErr :: TCTIdentifier -> TCMonad a
variableNotFoundErr (TCTIdentifier l id) = do
    varTrace <- definition ("'" <> id <> "' is accessed at:") l
    tcError $ ["Variable not in scope: " <> id] <> varTrace

typeCheckVar :: TypeEnv ->
                TCTIdentifier ->
                TCTType ->
                TCMonad (TCTIdentifier, Subst)
typeCheckVar (TypeEnv gamma) id@(TCTIdentifier l idName) tau = do
    case M.lookup idName gamma of
        Just sch -> do
            instScheme <- instantiate sch
            subst <- unify instScheme tau
            return (id, subst)
        Nothing -> variableNotFoundErr id

typeCheckFieldSelector :: TypeEnv ->
                          TCTFieldSelector ->
                          TCTType ->
                          TCMonad (TCTFieldSelector, Subst)
typeCheckFieldSelector gamma fd@(TCTFieldSelector loc id fields) tau = do
    alpha <- freshVar (getLoc id) "fd"
    (id', idSubst) <- typeCheckVar gamma id alpha

    (rType, fSubst) <- foldM typeCheckFields (idSubst $* alpha, mempty) fields

    let subst = fSubst <> idSubst
    uSubst <- unify rType (subst $* tau)
    return (TCTFieldSelector loc id' fields, uSubst <> subst)

    where
        toVar :: TCTField -> TCTIdentifier
        toVar (Hd loc) = TCTIdentifier loc "hd"
        toVar (Tl loc) = TCTIdentifier loc "tl"
        toVar (Fst loc) = TCTIdentifier loc "fst"
        toVar (Snd loc) = TCTIdentifier loc "snd"

        typeCheckFields :: (TCTType, Subst) ->
                           TCTField ->
                           TCMonad (TCTType, Subst)
        typeCheckFields (argType, prevSubst) field = do
            polyType <- freshVar (getLoc id) "fd"
            (_, fdSubst) <- typeCheckVar gamma (toVar field) polyType

            resultType <- freshVar (getLoc id) "fd"
            let funType = TCTFunType (getLoc field) [] argType resultType
            rSubst <- unify funType (fdSubst $* polyType)

            return (rSubst $* resultType, rSubst <> fdSubst)


typeCheckFunCall :: TypeEnv -> TCTFunCall -> TCTType -> TCMonad (TCTFunCall, Subst)
typeCheckFunCall gamma (TCTFunCall locF id@(TCTIdentifier locI _) args) tau = do
    (args', funType, argsSubst) <- foldrM typeCheckArgs ([], tau, mempty) args
    (id', idSubst) <- typeCheckVar gamma id funType

    return (TCTFunCall locF id' args', idSubst <> argsSubst)

    where
        typeCheckArgs :: TCTExpr ->
                         ([TCTExpr], TCTType, Subst) ->
                         TCMonad ([TCTExpr], TCTType, Subst)
        typeCheckArgs arg (exprs, funType, prevSubst) = do
            -- generate freshVar for each arg
            -- get a subst for each arg and compose them sequentially
            alpha <- freshVar (getLoc arg) "argCall"
            (arg', argSubst) <- typeCheckExpr (prevSubst $* gamma) arg alpha
            let subst = argSubst <> prevSubst
            return (arg' : exprs,
                    TCTFunType (getLoc arg) [] (subst $* alpha) funType,
                    subst)

typeCheckStmt :: TypeEnv ->
                 TCTStmt ->
                 TCTType ->
                 TCMonad (TCTStmt, Subst)
typeCheckStmt gamma stmt@(IfElseStmt loc cond thenStmts elseStmts) tau = do
    (_, condSubst) <- typeCheckExpr gamma cond (TCTBoolType $ getLoc cond)
    (_, thenSubst) <- typeCheckStmtList (condSubst $* gamma) thenStmts (condSubst $* tau)
    let combSubst = thenSubst <> condSubst
    (_, elseSubst) <- typeCheckStmtList (combSubst $* gamma) elseStmts (combSubst $* tau)
    return (stmt, combSubst <> elseSubst)

typeCheckStmt gamma stmt@(WhileStmt loc cond bodyStmts) tau = do
    (_, condSubst) <- typeCheckExpr gamma cond (TCTBoolType $ getLoc cond)
    (_, bodySubst) <- typeCheckStmtList (condSubst $* gamma) bodyStmts (condSubst $* tau)
    return (stmt, bodySubst <> condSubst)

typeCheckStmt gamma stmt@(AssignStmt loc field expr) tau = do
    alpha1 <- freshVar (getLoc field) "fd"
    (_, fieldSubst) <- typeCheckFieldSelector gamma field alpha1
    alpha2 <- freshVar (getLoc expr) "expr"
    (_, exprSubst) <- typeCheckExpr (fieldSubst $* gamma) expr alpha2
    let combSubst = exprSubst <> fieldSubst
    subst <- unify (combSubst $* alpha1) (combSubst $* alpha2)
    return (stmt, subst <> combSubst)

typeCheckStmt gamma stmt@(ReturnStmt loc Nothing) tau = do
    subst <- unify (TCTVoidType loc) tau
    return (stmt, mempty)

typeCheckStmt gamma stmt@(ReturnStmt loc (Just expr)) tau = do
    alpha <- freshVar loc "ret"
    (expr', exprSubst) <- typeCheckExpr gamma expr alpha
    subst <- unify (exprSubst $* alpha) (exprSubst $* tau)

    return (ReturnStmt loc (Just expr'), subst <> exprSubst)

typeCheckStmt gamma stmt@(FunCallStmt loc funCall) tau = do
    alpha <- freshVar loc "fcall"
    (funCall', funCallSubst) <- typeCheckFunCall gamma funCall alpha
    return (FunCallStmt loc funCall', funCallSubst)

typeCheckVarDecl :: TypeEnv ->
                    TCTVarDecl ->
                    TCMonad (TCTVarDecl, Subst)
typeCheckVarDecl gamma (TCTVarDecl loc tau (TCTIdentifier l i) e) = do
    alpha <- freshVar loc "v"
    (e', eSubst) <- typeCheckExpr gamma e alpha
    let mgt = eSubst $* alpha
    case tau of
        TCTVarType _ "" -> -- Use of Var
            return (TCTVarDecl loc mgt (TCTIdentifier l i) e', eSubst)
        _ -> do
            tSubst <- tau `isInstanceOf` generalise gamma mgt
            let subst = tSubst <> eSubst
            return (TCTVarDecl loc (subst $* alpha) (TCTIdentifier l i) e',
                    tSubst <> eSubst)

typeCheckStmtList :: TypeEnv ->
                     [TCTStmt] ->
                     TCTType ->
                     TCMonad ([TCTStmt], Subst)
typeCheckStmtList _ [] _ = return ([], mempty)
typeCheckStmtList gamma (st:sts) tau = do
    (st', substSt)  <- typeCheckStmt gamma st tau
    (sts', substSts) <- typeCheckStmtList (substSt $* gamma) sts (substSt $* tau)
    return (st':sts', substSts <> substSt)

typeCheckFunDecl ::  TypeEnv ->
                     TCTFunDecl ->
                     TCMonad (TCTFunDecl, Subst)
typeCheckFunDecl gamma@(TypeEnv gamma') (TCTFunDecl loc id@(TCTIdentifier idLoc idName) args tau funBody) = do
    retType <- freshVar idLoc "fun"
    alphaArgs <- mapM (\(TCTIdentifier l i) -> freshVar l "arg") args
    let expectedType = foldr (TCTFunType loc []) retType alphaArgs

    let newGamma = M.insert idName (liftToScheme expectedType) gamma'
    let newGamma' = foldr insertToGamma newGamma (zip args alphaArgs)
    (funBody', bSubst) <- typeCheckFunBody (TypeEnv newGamma') funBody retType

    case tau of
        TCTVarType _ "" ->
            return (TCTFunDecl loc id args (bSubst $* expectedType) funBody', bSubst)
        _ -> do
            tSubst <- tau `isInstanceOf` generalise gamma (bSubst $* expectedType)
            let subst = tSubst <> bSubst
            return (TCTFunDecl loc id args (subst $* tau) funBody', subst)

    where
        insertToGamma (TCTIdentifier l arg, t) g =
            M.insert arg (liftToScheme t) g

typeCheckFunBody :: TypeEnv -> TCTFunBody -> TCTType -> TCMonad (TCTFunBody, Subst)
typeCheckFunBody gamma (TCTFunBody loc varDecl stmts) tau = do
    (varDecl', newGamma, vSubst) <- foldM typeCheckVarDecls ([], gamma, mempty) varDecl

    (stmts', sSubst) <- typeCheckStmtList newGamma stmts (vSubst $* tau)

    return (TCTFunBody loc varDecl' stmts', sSubst <> vSubst)

    where
        typeCheckVarDecls :: ([TCTVarDecl], TypeEnv, Subst) ->
                             TCTVarDecl ->
                             TCMonad ([TCTVarDecl], TypeEnv, Subst)
        typeCheckVarDecls (prevVarDecl, prevGamma@(TypeEnv prevGamma'), prevSubst) varDecl = do
            (varDecl'@(TCTVarDecl loc t (TCTIdentifier idLoc id) _), subst) <- typeCheckVarDecl prevGamma varDecl
            let newGamma = subst $* TypeEnv (M.insert id (liftToScheme t) prevGamma')
            return (prevVarDecl ++ [varDecl'], newGamma, subst)

typeCheckTCT :: TCT -> TCMonad TCT
typeCheckTCT (TCT leafs) = do
    (leafs', _, subst) <- foldlM typeCheckLeaf ([], initGamma, mempty) leafs
    return $ subst $* TCT leafs'

    where
        typeCheckLeaf :: ([TCTLeaf], TypeEnv, Subst) -> TCTLeaf -> TCMonad ([TCTLeaf], TypeEnv, Subst)
        typeCheckLeaf (prevLeafs, prevGamma@(TypeEnv prevGamma'), subst) (TCTVar v)  = do
            (v'@(TCTVarDecl _ t (TCTIdentifier _ id) _), subst') <- typeCheckVarDecl prevGamma v
            let newGamma = subst' $* TypeEnv (M.insert id (liftToScheme t) prevGamma')
            return (prevLeafs ++ [TCTVar v'], newGamma, subst' <> subst)

        typeCheckLeaf (prevLeafs, prevGamma@(TypeEnv prevGamma'), subst) (TCTFun f)  = do
            (f'@(TCTFunDecl _ (TCTIdentifier _ id) _ t _), subst') <- typeCheckFunDecl prevGamma f
            let interGamma@(TypeEnv interGamma') = subst' $* prevGamma
            let newGamma = TypeEnv $ M.insert id (generalise interGamma t) interGamma'
            return (prevLeafs ++ [TCTFun f'], newGamma, subst' <> subst)
