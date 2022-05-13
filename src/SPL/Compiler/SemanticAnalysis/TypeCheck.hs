{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module SPL.Compiler.SemanticAnalysis.TypeCheck where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Data.Either.Extra (maybeToEither)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.List as L
import Data.Bifunctor
import Data.Foldable
import Data.Maybe
import Control.Monad.State
import Control.Applicative
import Control.Lens

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error
import SPL.Compiler.Common.Misc (wrapStateT)
import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TreeTransformer
import SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis (duplicateDefError)
import SPL.Compiler.SemanticAnalysis.TypeCheck.TCon
import SPL.Compiler.SemanticAnalysis.TypeCheck.Env (initGamma)
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify


sanitize :: TCTType -> TCMonad (TCTType, Subst)
sanitize t = do
    scheme <- wrapStateT (getEnv .~ mempty) (\old new -> new & getEnv .~ (old ^. getEnv)) (generalise t [])
    (\(t,c,s) -> (t,s)) <$> instantiate scheme

instantiate :: Scheme -> TCMonad (TCTType, [TCon], Subst)
instantiate (Scheme tv tcons t) = do
    newNames <- mapM (\v -> (v,) <$> freshVar (fromMaybe (getLoc t) (findLoc v t)) v) $ S.toList tv
    let subst = Subst . M.fromList $ newNames
    return (subst $* t, subst $* tcons, reverseSubst subst)

    where
        reverseSubst :: Subst -> Subst
        reverseSubst (Subst s) = Subst .
                                 M.fromList .
                                 map (\(k, TCTVarType l a) -> (a, TCTVarType l k)) .
                                 M.toList $ s
        findLoc :: TypeVar -> TCTType -> Maybe EntityLoc
        findLoc v1 (TCTVarType l v2)
            | v1 == v2 = Just l
            | otherwise = Nothing
        findLoc v1 (TCTListType _ t) = findLoc v1 t
        findLoc v1 (TCTTupleType _ t1 t2) =
            listToMaybe $ catMaybes [findLoc v1 t1, findLoc v1 t2]
        findLoc v1 (TCTFunType _ t1 t2) =
            listToMaybe $ catMaybes [findLoc v1 t1, findLoc v1 t2]
        findLoc _ _ = Nothing

freshVar :: EntityLoc -> Text -> TCMonad TCTType
freshVar loc prefix = do
    suffix <- T.pack . show <$> use getTvCounter
    getTvCounter += 1
    return $ TCTVarType loc (prefix <> suffix)

throwWarning :: Text -> TCMonad ()
throwWarning warn = getWarnings <>= [warn]

(<=*) :: TCTType -> Scheme -> TCMonad ()
(<=*) typ scheme = do
    subst <- use getSubst
    (typSanit, renameSubst) <- sanitize (subst $* typ)
    isInstanceOf renameSubst typSanit (subst $* scheme)

    where
        isInstanceOf _ TCTVoidType{} (Scheme _ _ TCTVoidType{}) = return ()
        isInstanceOf _ TCTIntType{}  (Scheme _ _ TCTIntType{}) = return ()
        isInstanceOf _ TCTCharType{} (Scheme _ _ TCTCharType{}) = return ()
        isInstanceOf _ TCTBoolType{} (Scheme _ _ TCTBoolType{}) = return ()
        isInstanceOf re v@(TCTVarType _ t) (Scheme tv _ v2@(TCTVarType l a))
            | S.member a tv = addSubst a (setLoc l v)
            | not (S.member a tv) && a == t = return mempty
            | otherwise = typeMismatchError (re $* v2) (re $* v)

        isInstanceOf re t (Scheme tv _ v2@(TCTVarType l a))
            | S.member a tv = addSubst a (setLoc l t)
            | S.null (freeVars t) = addSubst a (setLoc l t)
            | otherwise = typeMismatchError (re $* v2) (re $* t)

        isInstanceOf re (TCTListType _ t1) (Scheme tv _ (TCTListType _ t2)) =
           isInstanceOf re t1 (Scheme tv [] t2)

        isInstanceOf re (TCTTupleType _ a1 b1) (Scheme tv _ (TCTTupleType _ a2 b2)) = do
            isInstanceOf re a1 (Scheme tv [] a2)
            subst <- use getSubst
            isInstanceOf re b1 (Scheme tv [] $ subst $* b2)

        isInstanceOf re (TCTFunType _ a1 b1) (Scheme tv _ (TCTFunType _ a2 b2)) = do
            subst1 <- isInstanceOf re a1 (Scheme tv [] a2)
            subst <- use getSubst
            isInstanceOf re b1 (Scheme tv [] $ subst $* b2)

        isInstanceOf re t1 (Scheme _ _ t2) = typeMismatchError (re $* t2) (re $* t1)

checkNotInGamma :: TCTIdentifier -> DeclType -> TCMonad ()
checkNotInGamma id@(TCTIdentifier _ idName) declType = do
    TypeEnv env <- use getEnv
    let env' = M.filter ((==) declType . fst)
    when (M.member (idName, declType) env) $
        duplicateDefError id

variableNotFoundErr :: TCTIdentifier -> DeclType -> TCMonad a
variableNotFoundErr (TCTIdentifier l id) declType = do
    varTrace <- definition ("'" <> id <> "' is accessed at:") l
    tcError $ [T.pack (show declType) <> " not in scope: " <> id] <> varTrace

makeAbstractFunType :: TCTFunDecl -> TCMonad TCTType
makeAbstractFunType (TCTFunDecl loc id@(TCTIdentifier idLoc idName) args _ _ _) = do
    returnT <- freshVar idLoc "r"
    argTypes <- mapM (\(TCTIdentifier l i) -> freshVar l "a") args
    return $ foldr (TCTFunType loc) returnT argTypes

addFunTypeToEnv :: [TCon] -> TCTType -> TCTFunDecl -> TCMonad ()
addFunTypeToEnv tcons abstractType (TCTFunDecl _ id@(TCTIdentifier _ idName) _ _ _ _) = do
    checkNotInGamma id Fun
    getEnv %= (\(TypeEnv env) -> TypeEnv $
                    M.insert (idName, Fun) (Local, liftToScheme tcons abstractType) env)

addToEnv :: (Text, DeclType) -> (Scope, Scheme) -> TCMonad ()
addToEnv key value = do
    TypeEnv env <- use getEnv
    getEnv %= \(TypeEnv env) -> TypeEnv $ M.insert key value env

addArgsToEnv :: [(TCTType, TCTIdentifier)] -> TCMonad ()
addArgsToEnv args = do
    mapM_ (uncurry addToEnv . toKeyVal) args
    where
        toKeyVal (argT, TCTIdentifier l arg)  = ((arg, Var),(Arg, liftToScheme [] argT))

decomposeFunType :: TCTType -> ([TCTType], TCTType)
decomposeFunType (TCTFunType _ a r) =
    let (as, r') = decomposeFunType r in (a : as , r')
decomposeFunType x = ([], x)

getReturnType :: TCTType -> TCTType
getReturnType = snd . decomposeFunType

typeCheckExpr :: TCTExpr -> TCTType -> TCMonad TCTExpr
typeCheckExpr e@(IntExpr loc _) tau = do
    let expectedType = TCTIntType loc
    unify expectedType tau
    return e
typeCheckExpr e@(CharExpr loc _) tau = do
    let expectedType = TCTCharType loc
    unify expectedType tau
    return e
typeCheckExpr e@(BoolExpr loc _) tau = do
    let expectedType = TCTBoolType loc
    unify expectedType tau
    return e
typeCheckExpr (EmptyListExpr loc _) tau = do
    expectedType <- TCTListType loc <$> freshVar loc "l"
    unify expectedType tau
    return $ EmptyListExpr loc tau
typeCheckExpr e@(FunCallExpr f) tau = do
    f' <- typeCheckFunCall f tau
    return $ FunCallExpr f'
typeCheckExpr e@(FieldSelectExpr fs) tau = do
    fs' <- typeCheckFieldSelector fs tau
    return $ FieldSelectExpr fs'
typeCheckExpr e@(TupExpr loc e1 e2) tau = do
    t1 <- freshVar (getLoc e1) "t1"
    e1' <- typeCheckExpr e1 t1
    t2 <- freshVar (getLoc e2) "t2"
    e2' <- typeCheckExpr e2 t2
    let expectedType = TCTTupleType loc t1 t2
    unify expectedType tau
    return $ TupExpr loc e1' e2'
typeCheckExpr e@(OpExpr loc UnNeg e1) tau = do
    e1' <- typeCheckExpr e1 (TCTBoolType loc)
    let expectedType = TCTBoolType loc
    unify expectedType tau
    return $ OpExpr loc UnNeg e1'
typeCheckExpr e@(OpExpr loc UnMinus e1) tau = do
    e1' <- typeCheckExpr e1 (TCTIntType loc)
    let expectedType = TCTIntType loc
    unify expectedType tau
    return $ OpExpr loc UnMinus e1'
typeCheckExpr e@(Op2Expr loc e1 op e2) tau =
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
            e1' <- typeCheckExpr e1 (TCTIntType (getLoc e1))
            e2' <- typeCheckExpr e2 (TCTIntType (getLoc e2))
            let expectedType = TCTIntType loc
            unify expectedType tau
            return $ Op2Expr loc e1' op e2'

        handleBoolOp = do
            e1' <- typeCheckExpr e1 (TCTBoolType (getLoc e1))
            e2' <- typeCheckExpr e2 (TCTBoolType (getLoc e2))
            let expectedType = TCTBoolType loc
            unify expectedType tau
            return $ Op2Expr loc e1' op e2'

        handleConsOp = do
            c <- freshVar (getLoc e1) "c"
            e1' <- typeCheckExpr e1 c
            e2' <- typeCheckExpr e2 (TCTListType (getLoc e2) c)
            let expectedType = TCTListType (getLoc e) c
            unify expectedType tau
            return $ Op2Expr loc e1' op e2'

        handleOverloadedOp = do
            o <- freshVar (getLoc e1) "o"
            e1' <- typeCheckExpr e1 o
            e2' <- typeCheckExpr e2 o
            let constraint =
                    case op of
                        Equal -> TEq o
                        Nequal -> TEq o
                        Less -> TOrd o
                        Greater -> TOrd o
                        LessEq -> TOrd o
                        GreaterEq -> TOrd o
                        _ -> error "internal error: operator pattern should not occur"
            let expectedType = TCTBoolType loc
            tauSubst <- unify expectedType tau

            validateTCon [constraint]
            addTCon constraint

            return $ Op2Expr loc e1' op e2'

typeCheckVar :: TCTIdentifier -> DeclType -> TCTType -> TCMonad TCTIdentifier
typeCheckVar id@(TCTIdentifier l idName) declType tau = do
    (TypeEnv env) <- use getEnv
    let value =
            if declType == Both then
                M.lookup (idName, Var) env <|> M.lookup (idName, Fun) env
            else
                M.lookup (idName, declType) env

    case value of
        Just (scope, sch) -> do
            (instScheme, tcons, _) <- instantiate sch
            getTcons <>= if getLoc tcons == mempty then setLoc l tcons else tcons
            unify instScheme tau
            return id
        Nothing -> variableNotFoundErr id declType

typeCheckFieldSelector :: TCTFieldSelector -> TCTType -> TCMonad TCTFieldSelector
typeCheckFieldSelector fd@(TCTFieldSelector loc id _ fields) tau = do
    varT <- freshVar (getLoc id) "f"
    id' <- typeCheckVar id Both varT
    actualType <- foldM typeCheckFields varT fields
    unify tau actualType
    return $ TCTFieldSelector loc id' tau fields

    where
        toVar :: TCTField -> TCTIdentifier
        toVar (Hd loc) = TCTIdentifier loc "hd"
        toVar (Tl loc) = TCTIdentifier loc "tl"
        toVar (Fst loc) = TCTIdentifier loc "fst"
        toVar (Snd loc) = TCTIdentifier loc "snd"

        typeCheckFields :: TCTType -> TCTField -> TCMonad TCTType
        typeCheckFields argType field = do
            expectedType <- freshVar (getLoc id) "f"
            typeCheckVar (toVar field) Fun expectedType

            resultType <- freshVar (getLoc id) "f"
            let actualType = TCTFunType (getLoc field) argType resultType

            unify expectedType actualType
            return resultType

typeCheckFunCall :: TCTFunCall -> TCTType -> TCMonad TCTFunCall
typeCheckFunCall (TCTFunCall locF id@(TCTIdentifier locI _) _ _ args) tau = do
    (args', funType) <- foldrM typeCheckArgs ([], tau) args
    (id', funCallTcons) <-
        wrapStateT
            (getTcons .~ [])
            (\oldState newState -> newState & getTcons %~ ((oldState ^. getTcons) ++))
            (liftA2 (,) (typeCheckVar id Fun funType) (use getTcons))
    return $ TCTFunCall locF id' funType funCallTcons args'

    where
        typeCheckArgs :: TCTExpr -> ([TCTExpr], TCTType) -> TCMonad ([TCTExpr], TCTType)
        typeCheckArgs arg (exprs, resultType) = do
            argT <- freshVar (getLoc arg) "a"
            arg' <- typeCheckExpr arg argT
            return (arg' : exprs, TCTFunType (getLoc arg) argT resultType)

typeCheckStmt :: TCTStmt -> TCTType -> TCMonad TCTStmt
typeCheckStmt stmt@(IfElseStmt loc cond thenStmts elseStmts) tau = do
    cond' <- typeCheckExpr cond (TCTBoolType (getLoc cond))
    thenStmts' <- typeCheckStmtList thenStmts tau
    elseStmts' <- typeCheckStmtList elseStmts tau
    return $ IfElseStmt loc cond' thenStmts' elseStmts'

typeCheckStmt stmt@(WhileStmt loc cond bodyStmts) tau = do
    cond' <- typeCheckExpr cond (TCTBoolType (getLoc cond))
    bodyStmts' <- typeCheckStmtList bodyStmts tau
    return $ WhileStmt loc cond' bodyStmts'

typeCheckStmt stmt@(AssignStmt loc field expr) tau = do
    resultT <- freshVar (getLoc field) "f"
    field' <- typeCheckFieldSelector field resultT
    expr' <- typeCheckExpr expr resultT
    return $ AssignStmt loc field' expr'

typeCheckStmt stmt@(ReturnStmt loc Nothing) tau = do
    unify (TCTVoidType loc) tau
    return stmt

typeCheckStmt stmt@(ReturnStmt loc (Just expr)) tau = do
    returnT <- freshVar loc "r"
    expr' <- typeCheckExpr expr returnT
    unify returnT tau
    return $ ReturnStmt loc (Just expr')

typeCheckStmt stmt@(FunCallStmt loc funCall) tau = do
    resultT <- freshVar loc "f"
    funCall' <- typeCheckFunCall funCall resultT
    return $ FunCallStmt loc funCall'

typeCheckVarDecl :: TCTVarDecl -> TCMonad TCTVarDecl
typeCheckVarDecl (TCTVarDecl loc tau (TCTIdentifier l i) e) = do
    varT <- freshVar loc "v"
    e' <- typeCheckExpr e varT
    case tau of
        TCTVarType _ "" -> -- Use of Var keyword
            return $ TCTVarDecl loc varT (TCTIdentifier l i) e'
        _ -> do
            scheme <- generalise varT []
            tau <=* scheme
            return $ TCTVarDecl loc varT (TCTIdentifier l i) e'

typeCheckStmtList :: [TCTStmt] -> TCTType -> TCMonad [TCTStmt]
typeCheckStmtList [] _ = return []
typeCheckStmtList (st:sts) tau = do
    st'  <- typeCheckStmt st tau
    sts' <- typeCheckStmtList sts tau
    return $ st':sts'

shouldResultBeVoid :: TCTType -> TCTType -> Bool
shouldResultBeVoid resultType@(TCTVarType l v) funType
    | countOccurances v funType == 1 = True
    | otherwise = False
shouldResultBeVoid _ _ = False

countOccurances :: TypeVar -> TCTType -> Int
countOccurances var (TCTVarType _ nm)
    | var == nm = 1
    | otherwise = 0
countOccurances var (TCTListType _ t) = countOccurances var t
countOccurances var (TCTTupleType _ t1 t2) = countOccurances var t1 + countOccurances var t2
countOccurances var (TCTFunType _ t1 t2) = countOccurances var t1 + countOccurances var t2
countOccurances _ _ = 0

checkForVoidReturn :: TCTType -> TCTFunBody -> TCMonad TCTFunBody
checkForVoidReturn funType body@(TCTFunBody l varDecls stmts) = do
    subst <- use getSubst
    let funType' = subst $* funType
    let retType = getReturnType funType'

    if shouldResultBeVoid retType funType' then do
        let (TCTVarType l' v) = retType
        addSubst v (TCTVoidType l')
        return $ TCTFunBody l varDecls (stmts ++ [ReturnStmt l Nothing])
    else
        return body

typeCheckFunDecl :: TCTFunDecl -> TCTType -> TCMonad TCTFunDecl
typeCheckFunDecl f@(TCTFunDecl loc id@(TCTIdentifier idLoc idName) args tau _ body) abstractType = do
    initEnv <- (\(TypeEnv env) -> TypeEnv (M.delete (idName, Fun) env)) <$> use getEnv
    let (argTypes, retType) = decomposeFunType abstractType
    addArgsToEnv (zip argTypes args)
    body' <- typeCheckFunBody body retType >>= checkForVoidReturn abstractType

    tcons <- use getTcons
    case tau of
        TCTVarType _ "" -> pure ()
        _ -> do
            TypeEnv env <- use getEnv
            wrapStateT (getEnv .~ initEnv)
                       (\old new -> new & getEnv .~ (old ^. getEnv))
                       (do { funScheme <- generalise abstractType tcons;
                             tau <=* funScheme } )
            pure ()

    return $ TCTFunDecl loc id args abstractType tcons body'

typeCheckFunDecls :: [TCTFunDecl] -> TCMonad [TCTFunDecl]
typeCheckFunDecls [] = return []
typeCheckFunDecls funcs = do
    mapM_ (\(TCTFunDecl _ id _ _ _ _) -> checkNotInGamma id Fun) funcs
    initEnv <- use getEnv

    funTypes <- mapM makeAbstractFunType funcs
    mapM_ (uncurry (addFunTypeToEnv [])) (zip funTypes funcs)
    funcs' <- propagateTcons <$> zipWithM typeCheckSingleFun funcs funTypes

    getEnv .= initEnv
    getTcons .= []
    forM_ funcs' $
        \(TCTFunDecl _ (TCTIdentifier _ id) _ t tcons _) -> do
            scheme <- generalise t tcons
            addToEnv (id, Fun) (Global, scheme)

    pure funcs'

    where
        typeCheckSingleFun :: TCTFunDecl -> TCTType -> TCMonad TCTFunDecl
        typeCheckSingleFun fun funType = do
            getTcons .= []
            envBefore <- use getEnv
            fun' <- typeCheckFunDecl fun funType
            getEnv .= envBefore
            pure fun'

        propagateTcons :: [TCTFunDecl] -> [TCTFunDecl]
        propagateTcons funcs =
            let allTcons = L.nub $ concatMap (^. funTcons) funcs
            in flip map funcs $ \f ->
                f & funTcons .~ allTcons
                  & funBody %~ (\(TCTFunBody l v stmts) -> TCTFunBody l v (replaceTconsS allTcons stmts))

        funNames = funcs ^.. traversed.funId.idName

        replaceTconsS :: [TCon] -> [TCTStmt] -> [TCTStmt]
        replaceTconsS tc stmts =
            flip map stmts $
            \case
                IfElseStmt l e s1 s2 -> IfElseStmt l (replaceTconsE tc e) (replaceTconsS tc s1) (replaceTconsS tc s2)
                WhileStmt l e s -> WhileStmt l (replaceTconsE tc e) (replaceTconsS tc s)
                AssignStmt l fd e -> AssignStmt l fd (replaceTconsE tc e)
                FunCallStmt l fc -> FunCallStmt l (replaceTconsFC tc fc)
                ReturnStmt l me -> ReturnStmt l (replaceTconsE tc <$> me)

        replaceTconsE :: [TCon] -> TCTExpr -> TCTExpr
        replaceTconsE tc (FunCallExpr f) = FunCallExpr (replaceTconsFC tc f)
        replaceTconsE tc (OpExpr l op e) = OpExpr l op (replaceTconsE tc e)
        replaceTconsE tc (Op2Expr l e1 op e2) = Op2Expr l (replaceTconsE tc e1) op (replaceTconsE tc e2)
        replaceTconsE tc (TupExpr l e1 e2) = TupExpr l (replaceTconsE tc e1) (replaceTconsE tc e2)
        replaceTconsE _ e = e

        replaceTconsFC :: [TCon] -> TCTFunCall -> TCTFunCall
        replaceTconsFC tc fc
            | (fc ^. funCallId.idName) `L.elem` funNames = fc & funCallTcons .~ tc
            | otherwise = fc

typeCheckFunBody :: TCTFunBody -> TCTType -> TCMonad TCTFunBody
typeCheckFunBody (TCTFunBody loc varDecls stmts) tau = do
    varDecls' <- mapM typeCheckLocalVarDecl varDecls
    stmts' <- typeCheckStmtList stmts tau
    return $ TCTFunBody loc varDecls' stmts'

typeCheckLocalVarDecl :: TCTVarDecl -> TCMonad TCTVarDecl
typeCheckLocalVarDecl varDecl@(TCTVarDecl _ _ id _) = do
    checkNotInGamma id Var
    varDecl'@(TCTVarDecl loc t (TCTIdentifier idLoc id) _) <- typeCheckVarDecl varDecl
    getEnv %= \(TypeEnv env) -> TypeEnv (M.insert (id, Var) (Local, liftToScheme [] t) env)
    return varDecl'

typeCheckGlobVarDecl :: TCTVarDecl -> TCMonad TCTVarDecl
typeCheckGlobVarDecl v@(TCTVarDecl _ _ id _)  = do
    checkNotInGamma id Var
    v'@(TCTVarDecl _ t (TCTIdentifier _ id) _) <- typeCheckVarDecl v
    addToEnv (id, Var) (Global, liftToScheme [] t)
    return v'

typeCheckTCT :: TCT -> TCMonad TCT
typeCheckTCT (TCT varDecls funDecls) = do
    getEnv .= initGamma
    varDecls' <- mapM typeCheckGlobVarDecl varDecls
    funDecls' <- mapM typeCheckFunDecls funDecls

    -- validateTCon (subst $* tcon)
    -- TODO: validate type constraints here `tcon`
    -- variable declarations containing non concrete TCon should
    -- be invalid

    subst <- use getSubst
    let tct' = TCT (subst $* varDecls') (subst $* funDecls')

    sanityCheck tct'
    pure tct'

sanityCheck :: TCT -> TCMonad ()
sanityCheck (TCT varDecls funDecls) = do
    forM_ varDecls $ \varDecl -> do
        let t = varDecl ^. varDeclType
            ftv = freeVars t
        unless (S.null ftv) $
            definition (
                "Ambigous type variables " <>
                "[" <> T.intercalate ", " (S.toList ftv) <> "] " <>
                "found in type " <> T.pack (show t) <> ":") t
            >>= tcError

    if isJust main then do
        let (Just main') = main

        forM_ (main' ^. funTcons) $ \tcon ->
            unless (S.null (freeVars tcon)) $
                tconError tcon >>= tcError
    else
        throwWarning "No 'main' function found. Program will not execute"
    where
        main = L.find (\f -> f ^. funId.idName == "main") . concat $ funDecls
