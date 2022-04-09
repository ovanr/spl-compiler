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
import SPL.Compiler.TypeChecker.TCon
import SPL.Compiler.TypeChecker.Env (initGamma)
import SPL.Compiler.TypeChecker.Unify


sanitize :: TCTType -> TCMonad (TCTType, Subst)
sanitize = instantiate . generalise mempty

instantiate :: Scheme -> TCMonad (TCTType, Subst)
instantiate (Scheme tv t) = do
    newNames <- mapM (\v -> (v,) <$> freshVar (fromMaybe (getLoc t) (findLoc v t)) v) $ S.toList tv
    let subst = Subst . M.fromList $ newNames
    return (subst $* t, subst)

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
isInstanceOf (TCTVoidType _) (Scheme _ (TCTVoidType _)) = return mempty
isInstanceOf (TCTIntType _)  (Scheme _ (TCTIntType _)) = return mempty
isInstanceOf (TCTCharType _) (Scheme _ (TCTCharType _)) = return mempty
isInstanceOf (TCTBoolType _) (Scheme _ (TCTBoolType _)) = return mempty
isInstanceOf v@(TCTVarType _ t) (Scheme tv v2@(TCTVarType l a))
    | S.member a tv = return . Subst $ M.singleton a (setLoc l v)
    | not (S.member a tv) && a == t = return mempty
    | otherwise = typeMismatchError v2 v

isInstanceOf t (Scheme tv v@(TCTVarType l a))
    | S.member a tv = return . Subst $ M.singleton a (setLoc l t)
    | otherwise = typeMismatchError v t

isInstanceOf (TCTListType _ t1) (Scheme tv (TCTListType _ t2)) =
   isInstanceOf t1 (Scheme tv t2)

isInstanceOf (TCTTupleType _ a1 b1) (Scheme tv (TCTTupleType _ a2 b2)) = do
    subst1 <- isInstanceOf a1 (Scheme tv a2)
    subst2 <- isInstanceOf b1 (Scheme tv $ subst1 $* b2)
    return $ subst2 <> subst1

isInstanceOf (TCTFunType _ _ a1 b1) (Scheme tv (TCTFunType _ _ a2 b2)) = do
    subst1 <- isInstanceOf a1 (Scheme tv a2)
    subst2 <- isInstanceOf b1 (Scheme tv $ subst1 $* b2)
    return $ subst2 <> subst1

isInstanceOf t1 (Scheme _ t2) = typeMismatchError t2 t1

typeCheckExpr :: TypeEnv ->
                 TCTExpr ->
                 TCTType ->
                 TCMonad (Set TCon, TCTExpr, Subst)
typeCheckExpr _ e@(IntExpr loc _) tau = do
    let expectedType = TCTIntType loc
    subst <- unify expectedType tau
    return (mempty, e, subst)
typeCheckExpr _ e@(CharExpr loc _) tau = do
    let expectedType = TCTCharType loc
    subst <- unify expectedType tau
    return (mempty, e, subst)
typeCheckExpr _ e@(BoolExpr loc _) tau = do
    let expectedType = TCTBoolType loc
    subst <- unify expectedType tau
    return (mempty, e, subst)
typeCheckExpr _ e@(EmptyListExpr loc) tau = do
    expectedType <- TCTListType loc <$> freshVar loc "l"
    subst <- unify expectedType tau
    return (mempty, e, subst)
typeCheckExpr gamma e@(FunCallExpr f) tau = do
    (tcon, f', fSubst) <- typeCheckFunCall gamma f tau
    return (tcon, FunCallExpr f', fSubst)
typeCheckExpr gamma e@(FieldSelectExpr fs) tau = do
    (tcon, fs', fSubst) <- typeCheckFieldSelector gamma fs tau
    return (tcon, FieldSelectExpr fs', fSubst)
typeCheckExpr gamma e@(TupExpr loc e1 e2) tau = do
    alpha1 <- freshVar (getLoc e1) "tup1"
    (tcon1, e1', e1Subst) <- typeCheckExpr gamma e1 alpha1
    alpha2 <- freshVar (getLoc e2) "tup2"
    (tcon2, e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 alpha2
    let eSubst = e2Subst <> e1Subst
    let expectedType = eSubst $* TCTTupleType loc alpha1 alpha2
    tauSubst <- unify expectedType (eSubst $* tau)
    let subst = tauSubst <> eSubst
    return (subst $* tcon1 <> tcon2, TupExpr loc e1' e2', subst)
typeCheckExpr gamma e@(OpExpr loc UnNeg e1) tau = do
    (tcon, e1', e1Subst) <- typeCheckExpr gamma e1 (TCTBoolType loc)
    let expectedType = TCTBoolType loc
    tauSubst <- unify expectedType (e1Subst $* tau)
    return (tauSubst $* tcon, OpExpr loc UnNeg e1', tauSubst <> e1Subst)
typeCheckExpr gamma e@(OpExpr loc UnMinus e1) tau = do
    (tcon, e1', e1Subst) <- typeCheckExpr gamma e1 (TCTIntType loc)
    let expectedType = TCTIntType loc
    tauSubst <- unify expectedType (e1Subst $* tau)
    return (tauSubst $* tcon, OpExpr loc UnMinus e1', tauSubst <> e1Subst)
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
        _ -> handleOverloadedOp

    where
        handleIntOp = do
            (tcon1, e1', e1Subst) <- typeCheckExpr gamma e1 (TCTIntType $ getLoc e1)
            (tcon2, e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 (TCTIntType $ getLoc e2)
            let eSubst = e2Subst <> e1Subst
            let expectedType = TCTIntType loc
            tauSubst <- unify expectedType (eSubst $* tau)
            let subst = tauSubst <> eSubst
            return (subst $* tcon1 <> tcon2, Op2Expr loc e1' op e2', subst)

        handleBoolOp = do
            (tcon1, e1', e1Subst) <- typeCheckExpr gamma e1 (TCTBoolType $ getLoc e1)
            (tcon2, e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2 (TCTBoolType $ getLoc e2)
            let eSubst = e2Subst <> e1Subst
            let expectedType = TCTBoolType loc
            tauSubst <- unify expectedType (eSubst $* tau)
            return (tcon1 <> tcon2, Op2Expr loc e1' op e2', tauSubst <> eSubst)

        handleConsOp = do
            alpha <- freshVar (getLoc e1) "cons"
            (tcon1, e1', e1Subst) <- typeCheckExpr gamma e1 alpha
            (tcon2, e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2
                                            (TCTListType (getLoc e2) (e1Subst $* alpha))
            let eSubst = e2Subst <> e1Subst
            let expectedType = eSubst $* TCTListType (getLoc e) alpha
            tauSubst <- unify expectedType (eSubst $* tau)
            let subst = tauSubst <> eSubst
            return (subst $* tcon1 <> tcon2, Op2Expr loc e1' op e2', subst)

        handleOverloadedOp = do
            alpha <- freshVar (getLoc e1) "overl"
            (tcon1, e1', e1Subst) <- typeCheckExpr gamma e1 alpha
            (tcon2, e2', e2Subst) <- typeCheckExpr (e1Subst $* gamma) e2
                                            (e1Subst $* alpha)
            let eSubst = e2Subst <> e1Subst
            let argType = eSubst $* alpha
            let constraint =
                    case op of
                        Equal -> TEq argType
                        Nequal -> TEq argType
                        Less -> TOrd argType
                        Greater -> TOrd argType
                        LessEq -> TOrd argType
                        GreaterEq -> TOrd argType
                        _ -> error "internal error: operator pattern should not occur"
            let expectedType = TCTBoolType loc
            tauSubst <- unify expectedType (eSubst $* tau)
            let subst = tauSubst <> eSubst

            let newCon = subst $* S.insert constraint (tcon1 <> tcon2)
            validateTCon newCon

            return (newCon,
                    Op2Expr loc e1' op e2',
                    subst)

variableNotFoundErr :: TCTIdentifier -> TCMonad a
variableNotFoundErr (TCTIdentifier l id) = do
    varTrace <- definition ("'" <> id <> "' is accessed at:") l
    tcError $ ["Variable not in scope: " <> id] <> varTrace

typeCheckVar :: TypeEnv ->
                TCTIdentifier ->
                TCTType ->
                TCMonad (Set TCon, TCTIdentifier, Subst)
typeCheckVar (TypeEnv gamma) id@(TCTIdentifier l idName) tau = do
    case M.lookup idName gamma of
        Just sch -> do
            (instScheme, _) <- instantiate sch
            subst <- unify instScheme tau
            return (getTypeCon (subst $* instScheme), id, subst)
        Nothing -> variableNotFoundErr id

typeCheckFieldSelector :: TypeEnv ->
                          TCTFieldSelector ->
                          TCTType ->
                          TCMonad (Set TCon, TCTFieldSelector, Subst)
typeCheckFieldSelector gamma fd@(TCTFieldSelector loc id fields) tau = do
    alpha <- freshVar (getLoc id) "fd"
    (tcon, id', idSubst) <- typeCheckVar gamma id alpha

    (rType, fSubst) <- foldM typeCheckFields (idSubst $* alpha, mempty) fields

    let fidSubst = fSubst <> idSubst
    rSubst <- unify rType (fidSubst $* tau)
    let subst = rSubst <> fidSubst
    return (subst $* tcon, TCTFieldSelector loc id' fields, subst)

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
            (_, _, fdSubst) <- typeCheckVar gamma (toVar field) polyType

            resultType <- freshVar (getLoc id) "fd"
            let funType = TCTFunType (getLoc field) mempty argType resultType
            rSubst <- unify funType (fdSubst $* polyType)

            return (rSubst $* resultType, rSubst <> fdSubst)


typeCheckFunCall :: TypeEnv -> TCTFunCall -> TCTType -> TCMonad (Set TCon, TCTFunCall, Subst)
typeCheckFunCall gamma (TCTFunCall locF id@(TCTIdentifier locI _) args) tau = do
    (tcon1, args', funType, argsSubst) <- foldrM typeCheckArgs (mempty, [], tau, mempty) args
    (tcon2, id', idSubst) <- typeCheckVar gamma id funType
    let subst = idSubst <> argsSubst
    return (subst $* tcon1 <> tcon2, TCTFunCall locF id' args', subst)

    where
        typeCheckArgs :: TCTExpr ->
                         (Set TCon, [TCTExpr], TCTType, Subst) ->
                         TCMonad (Set TCon, [TCTExpr], TCTType, Subst)
        typeCheckArgs arg (prevTCon, exprs, funType, prevSubst) = do
            -- generate freshVar for each arg
            -- get a subst for each arg and compose them sequentially
            alpha <- freshVar (getLoc arg) "argCall"
            (tcon1, arg', argSubst) <- typeCheckExpr (prevSubst $* gamma) arg alpha
            let subst = argSubst <> prevSubst
            return (subst $* tcon1 <> prevTCon,
                    arg' : exprs,
                    TCTFunType (getLoc arg) mempty (subst $* alpha) funType,
                    subst)

typeCheckStmt :: TypeEnv ->
                 TCTStmt ->
                 TCTType ->
                 TCMonad (Set TCon, TCTStmt, Subst)
typeCheckStmt gamma stmt@(IfElseStmt loc cond thenStmts elseStmts) tau = do
    (tcon1, _, condSubst) <- typeCheckExpr gamma cond (TCTBoolType $ getLoc cond)
    (tcon2, _, thenSubst) <- typeCheckStmtList (condSubst $* gamma) thenStmts (condSubst $* tau)
    let combSubst = thenSubst <> condSubst
    (tcon3, _, elseSubst) <- typeCheckStmtList (combSubst $* gamma) elseStmts (combSubst $* tau)
    let subst = elseSubst <> combSubst
    return (subst $* tcon1 <> tcon2 <> tcon3, stmt, subst)

typeCheckStmt gamma stmt@(WhileStmt loc cond bodyStmts) tau = do
    (tcon1, _, condSubst) <- typeCheckExpr gamma cond (TCTBoolType $ getLoc cond)
    (tcon2, _, bodySubst) <- typeCheckStmtList (condSubst $* gamma) bodyStmts (condSubst $* tau)
    let subst = bodySubst <> condSubst
    return (subst $* tcon1 <> tcon2, stmt, subst)

typeCheckStmt gamma stmt@(AssignStmt loc field expr) tau = do
    alpha1 <- freshVar (getLoc field) "fd"
    (tcon1, _, fieldSubst) <- typeCheckFieldSelector gamma field alpha1
    alpha2 <- freshVar (getLoc expr) "expr"
    (tcon2, _, exprSubst) <- typeCheckExpr (fieldSubst $* gamma) expr alpha2
    let combSubst = exprSubst <> fieldSubst
    aSubst <- unify (combSubst $* alpha1) (combSubst $* alpha2)
    let subst = aSubst <> combSubst
    return (subst $* tcon1 <> tcon2, stmt, subst)

typeCheckStmt gamma stmt@(ReturnStmt loc Nothing) tau = do
    subst <- unify (TCTVoidType loc) tau
    return (mempty, stmt, mempty)

typeCheckStmt gamma stmt@(ReturnStmt loc (Just expr)) tau = do
    alpha <- freshVar loc "ret"
    (tcon, expr', exprSubst) <- typeCheckExpr gamma expr alpha
    tauSubst <- unify (exprSubst $* alpha) (exprSubst $* tau)
    let subst = tauSubst <> exprSubst
    return (subst $* tcon, ReturnStmt loc (Just expr'), subst)

typeCheckStmt gamma stmt@(FunCallStmt loc funCall) tau = do
    alpha <- freshVar loc "fcall"
    (tcon, funCall', funCallSubst) <- typeCheckFunCall gamma funCall alpha
    return (tcon, FunCallStmt loc funCall', funCallSubst)

typeCheckVarDecl :: TypeEnv ->
                    TCTVarDecl ->
                    TCMonad (Set TCon, TCTVarDecl, Subst)
typeCheckVarDecl gamma (TCTVarDecl loc tau (TCTIdentifier l i) e) = do
    alpha <- freshVar loc "v"
    (tcon, e', eSubst) <- typeCheckExpr gamma e alpha
    let mgt = eSubst $* alpha
    case tau of
        TCTVarType _ "" -> -- Use of Var
            return (tcon, TCTVarDecl loc mgt (TCTIdentifier l i) e', eSubst)
        _ -> do
            (tauSanit, _) <- sanitize tau
            tauSubst <- tauSanit `isInstanceOf` generalise gamma mgt
            let subst = tauSubst <> eSubst
            return (tauSubst $* tcon,
                    TCTVarDecl loc (subst $* alpha) (TCTIdentifier l i) e',
                    subst)

typeCheckStmtList :: TypeEnv ->
                     [TCTStmt] ->
                     TCTType ->
                     TCMonad (Set TCon, [TCTStmt], Subst)
typeCheckStmtList _ [] _ = return (mempty, [], mempty)
typeCheckStmtList gamma (st:sts) tau = do
    (tcon1, st', substSt)  <- typeCheckStmt gamma st tau
    (tcon2, sts', substSts) <- typeCheckStmtList (substSt $* gamma) sts (substSt $* tau)
    let subst = substSts <> substSt
    return (subst $* tcon1 <> tcon2, st':sts', subst)

typeCheckFunDecl ::  TypeEnv ->
                     TCTFunDecl ->
                     TCMonad (TCTFunDecl, Subst)
typeCheckFunDecl gamma@(TypeEnv gamma') (TCTFunDecl loc id@(TCTIdentifier idLoc idName) args tau funBody) = do
    retType <- freshVar idLoc "fun"
    alphaArgs <- mapM (\(TCTIdentifier l i) -> freshVar l "arg") args
    let expectedType = foldr (TCTFunType loc mempty) retType alphaArgs

    let newGamma = M.insert idName (liftToScheme expectedType) gamma'
    let newGamma' = foldr insertToGamma newGamma (zip args alphaArgs)
    (tcon, funBody', bSubst) <- typeCheckFunBody (TypeEnv newGamma') funBody retType
    let expectedType' = bSubst $* foldr (TCTFunType loc tcon) retType alphaArgs


    case tau of
        TCTVarType _ "" -> do
            validateTCon tcon
            return (TCTFunDecl loc id args expectedType' funBody', bSubst)
        _ -> do
            (tauSanit, _) <- sanitize tau
            tSubst <- tauSanit `isInstanceOf` generalise gamma expectedType'
            validateTCon (tSubst $* tcon)
            return (TCTFunDecl loc id args (tSubst $* expectedType') funBody', tSubst <> bSubst)

    where
        insertToGamma (TCTIdentifier l arg, t) g =
            M.insert arg (liftToScheme t) g

typeCheckFunBody :: TypeEnv -> TCTFunBody -> TCTType -> TCMonad (Set TCon, TCTFunBody, Subst)
typeCheckFunBody gamma (TCTFunBody loc varDecl stmts) tau = do
    (tcon1, varDecl', newGamma, vSubst) <- foldM typeCheckVarDecls (mempty, [], gamma, mempty) varDecl

    (tcon2, stmts', sSubst) <- typeCheckStmtList newGamma stmts (vSubst $* tau)
    let subst = sSubst <> vSubst

    return (subst $* tcon1 <> tcon2, TCTFunBody loc varDecl' stmts', subst)

    where
        typeCheckVarDecls :: (Set TCon, [TCTVarDecl], TypeEnv, Subst) ->
                             TCTVarDecl ->
                             TCMonad (Set TCon, [TCTVarDecl], TypeEnv, Subst)
        typeCheckVarDecls (tcon1, prevVarDecl, prevGamma@(TypeEnv prevGamma'), prevSubst) varDecl = do
            (tcon2, varDecl'@(TCTVarDecl loc t (TCTIdentifier idLoc id) _), vSubst) <- typeCheckVarDecl prevGamma varDecl
            let newGamma = vSubst $* TypeEnv (M.insert id (liftToScheme t) prevGamma')
            let subst = vSubst <> prevSubst
            return (subst $* tcon1 <> tcon2, prevVarDecl ++ [varDecl'], newGamma, subst)

typeCheckTCT :: TCT -> TCMonad TCT
typeCheckTCT (TCT leafs) = do
    (tcon, leafs', _, subst) <- foldlM typeCheckLeaf (mempty, [], initGamma, mempty) leafs
    validateTCon (subst $* tcon)
    -- TODO: validate type constraints here `tcon`
    -- variable declarations containing non concrete TCon should
    -- be invalid
    return $ subst $* TCT leafs'

    where
        typeCheckLeaf :: (Set TCon, [TCTLeaf], TypeEnv, Subst) ->
                         TCTLeaf ->
                         TCMonad (Set TCon, [TCTLeaf], TypeEnv, Subst)
        typeCheckLeaf (prevCon, prevLeafs, prevGamma@(TypeEnv prevGamma'), prevSubst) (TCTVar v)  = do
            (tcon, v'@(TCTVarDecl _ t (TCTIdentifier _ id) _), vSubst) <- typeCheckVarDecl prevGamma v
            let newGamma = vSubst $* TypeEnv (M.insert id (liftToScheme t) prevGamma')
            let subst = vSubst <> prevSubst
            return (subst $* tcon <> prevCon, prevLeafs ++ [TCTVar v'], newGamma, subst)

        typeCheckLeaf (tcon, prevLeafs, prevGamma@(TypeEnv prevGamma'), prevSubst) (TCTFun f)  = do
            (f'@(TCTFunDecl _ (TCTIdentifier _ id) _ t _), fSubst) <- typeCheckFunDecl prevGamma f
            let interGamma@(TypeEnv interGamma') = fSubst $* prevGamma
            let newGamma = TypeEnv $ M.insert id (generalise interGamma t) interGamma'
            let subst = fSubst <> prevSubst
            return (subst $* tcon, prevLeafs ++ [TCTFun f'], newGamma, subst)
