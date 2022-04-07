{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module SPL.Compiler.TypeChecker.TypeCheck where

import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Either.Extra (maybeToEither)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Bifunctor
import Data.Foldable
import Control.Monad.State
import Control.Lens

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.Unify
import qualified Control.Lens.Internal.Deque as Map

type TCMonad a = StateT TypeCheckState (Either Error) a

tcError = lift . Left . pure

newtype TypeCheckState =
    TypeCheckState {
        _tvCounter :: Integer
    }

makeLenses 'TypeCheckState

sanitize :: TCTType -> TCMonad TCTType
sanitize = instantiate . liftToScheme

instantiate :: Scheme -> TCMonad TCTType
instantiate (Scheme tv t) = do
    newNames <- mapM (\v -> (v,) <$> freshVar (getLoc t) v) $ S.toList tv
    let subst = Subst . M.fromList $ newNames
    return $ subst $* t

freshVar :: EntityLoc -> Text -> TCMonad TCTType
freshVar loc prefix = do
    suffix <- T.pack . show <$> use tvCounter
    tvCounter += 1
    return $ TCTVarType loc ("'" <> prefix <> suffix)

isInstanceOf :: TCTType -> Scheme -> TCMonad Subst
isInstanceOf t sch = do
    sanitizedT <- sanitize t
    lift $ isInstanceOf' sanitizedT sch

    where
        isInstanceOf' :: TCTType -> Scheme -> Either Error Subst
        isInstanceOf' (TCTVoidType _) (Scheme _ (TCTVoidType _)) = Right mempty
        isInstanceOf' (TCTIntType _)  (Scheme _ (TCTIntType _)) = Right mempty
        isInstanceOf' (TCTCharType _) (Scheme _ (TCTCharType _)) = Right mempty
        isInstanceOf' (TCTBoolType _) (Scheme _ (TCTBoolType _)) = Right mempty
        isInstanceOf' (TCTVarType _ t) (Scheme tv (TCTVarType l a)) =
            if not $ S.member a tv && a == t then
                return mempty
            else
                Left $ typeMismatchError t a

        isInstanceOf' t (Scheme tv v@(TCTVarType l a)) =
            if S.member a tv then
                Right . Subst $ M.singleton a (setLoc l t)
            else
                Left $ typeMismatchError t v

        isInstanceOf' (TCTListType _ t1) (Scheme tv (TCTListType _ t2)) =
           isInstanceOf' t1 (Scheme tv t2)

        isInstanceOf' (TCTTupleType _ a1 b1) (Scheme tv (TCTTupleType _ a2 b2)) = do
            subst1 <- isInstanceOf' a1 (Scheme tv a2)
            subst2 <- isInstanceOf' b1 (Scheme tv $ subst1 $* b2)
            Right $ subst2 <> subst1

        isInstanceOf' (TCTFunType _ _ a1 b1) (Scheme tv (TCTFunType _ _ a2 b2)) = do
            subst1 <- isInstanceOf' a1 (Scheme tv a2)
            subst2 <- isInstanceOf' a2 (Scheme tv $ subst1 $* b2)
            Right $ subst2 <> subst1

        isInstanceOf' t1 t2 = Left $ typeMismatchError t1 t2

typeCheckExpr :: TypeEnv ->
                 TCTExpr ->
                 TCTType ->
                 TCMonad (TCTExpr, Subst)
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
    expectedType <- TCTListType loc <$> freshVar loc "l"
    subst <- lift $ unify tau expectedType
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
            alpha <- freshVar (getLoc e1) "cons"
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

-- forall c. c ->> forall c. forall a. a -> Void ->> forall c a. a -> Void ->> forall a. a -> Void
-- forall a. a -> Void
-- [ c |-> forall a. a -> Void ] 

typeCheckVar :: TypeEnv ->
                TCTIdentifier ->
                TCTType ->
                TCMonad (TCTIdentifier, Subst)
typeCheckVar (TypeEnv gamma) id@(TCTIdentifier l idName) tau = do
    case M.lookup idName gamma of
        Just sch -> do
            instScheme <- instantiate sch
            subst <- lift $ unify instScheme tau
            return (id, subst)
        Nothing -> do
            tcError $ "Variable not found " <> idName

-- assume gamma contains = hd :: forall a. [a] -> a, tl :: forall a. [a] -> [a], fst :: forall a b. (a,b) -> a
--                         snd :: forall a b. (a,b) -> b
typeCheckFieldSelector :: TypeEnv ->
                          TCTFieldSelector ->
                          TCTType ->
                          TCMonad (TCTFieldSelector, Subst)
typeCheckFieldSelector gamma fd@(TCTFieldSelector loc id fields) tau = do
    alpha <- freshVar (getLoc id) "fd"
    (id', idSubst) <- typeCheckVar gamma id alpha
    (rType, fSubst) <- foldM typeCheckFields (idSubst $* alpha, mempty) fields
    
    let subst = fSubst <> idSubst
    uSubst <- lift $ unify rType (subst $* tau)
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
            rSubst <- lift $ unify funType (fdSubst $* polyType)

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
            alpha <- freshVar (getLoc arg) "arg"
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
    subst <- lift $ unify (combSubst $* alpha1) (combSubst $* alpha2)
    return (stmt, subst <> combSubst)

typeCheckStmt gamma stmt@(ReturnStmt loc Nothing) tau = do
    subst <- lift $ unify tau (TCTVoidType loc)
    return (stmt, mempty)

typeCheckStmt gamma stmt@(ReturnStmt loc (Just expr)) tau = do
    alpha <- freshVar loc "ret"
    (_, exprSubst) <- typeCheckExpr gamma expr alpha
    subst <- lift $ unify (exprSubst $* alpha) (exprSubst $* tau)
    return (stmt, subst <> exprSubst)

typeCheckStmt gamma stmt@(FunCallStmt loc funCall) tau = do
    alpha <- freshVar loc "fcall"
    (funCall', funCallSubst) <- typeCheckFunCall gamma funCall alpha
    subst <- lift $ unify (funCallSubst $* alpha) (funCallSubst $* tau)
    return (FunCallStmt loc funCall', subst <> funCallSubst)

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
    (_, substSt)  <- typeCheckStmt gamma st tau
    (_, substSts) <- typeCheckStmtList (substSt $* gamma) sts (substSt $* tau)
    return (st:sts, substSt <> substSts)

typeCheckFunDecl ::  TypeEnv ->
                     TCTFunDecl ->
                     TCMonad (TCTFunDecl, Subst)
typeCheckFunDecl (TypeEnv gamma) (TCTFunDecl loc id@(TCTIdentifier idLoc idName) args tau funBody) = do
    retType <- freshVar idLoc "fun"
    alphaArgs <- mapM (\(TCTIdentifier l i) -> freshVar l "arg") args
    let expectedType = foldr (TCTFunType loc []) retType alphaArgs

    newGamma <- return $ M.insert idName expectedType
    newGamma <- return $ foldr insertToGamma gamma (zip args alphaArgs)
    (funBody', bSubst) <- typeCheckFunBody (TypeEnv newGamma) funBody retType

    case tau of
        TCTVarType _ "" ->
            return (TCTFunDecl loc id args (bSubst $* tau) funBody', bSubst)
        _ -> do
            tSubst <- tau `isInstanceOf` generalise (TypeEnv newGamma) (bSubst $* expectedType)
            let subst = tSubst <> bSubst
            return (TCTFunDecl loc id args (subst $* tau) funBody', subst)

    where
        insertToGamma (TCTIdentifier l arg, t) g =
            M.insert arg (generalise (TypeEnv g) t) g

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
            let combSubst = subst' <> subst
            let newGamma = subst' $* TypeEnv (M.insert id (liftToScheme t) prevGamma')
            return (prevLeafs ++ [TCTVar v'], newGamma, combSubst)

        typeCheckLeaf (prevLeafs, prevGamma@(TypeEnv prevGamma'), subst) (TCTFun f)  = do
            (f'@(TCTFunDecl _ (TCTIdentifier _ id) _ t _), subst') <- typeCheckFunDecl prevGamma f 
            prevGamma@(TypeEnv prevGamma') <- return $ subst $* prevGamma
            let combSubst = subst' <> subst
            let newGamma = TypeEnv $ M.insert id (liftToScheme t) prevGamma'
            return (prevLeafs ++ [TCTFun f'], newGamma, combSubst)

builtinLoc = EntityLoc (0,0) (0,0)

printEnv :: (Text, Scheme)
printEnv = ("print", Scheme (S.fromList ["a"]) (TCTFunType builtinLoc [] (TCTVarType builtinLoc "a") (TCTVoidType builtinLoc)))

initGamma :: TypeEnv 
initGamma = TypeEnv $ M.fromList [printEnv]
