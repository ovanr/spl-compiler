{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module SPL.Compiler.SemanticAnalysis.TypeCheck where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Data.Graph ( SCC(..) )
import Data.Either.Extra (maybeToEither)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.List as L
import Data.Bifunctor ( Bifunctor(bimap) )
import Data.Foldable ( forM_ )
import Data.Maybe ()
import Control.Monad.State ( foldM, unless, zipWithM, forM )
import Control.Applicative ()
import Control.Lens ( (^.), use, (.=), traversed, (+=) )

import SPL.Compiler.Common.EntityLocation ( Locatable(getLoc, setLoc) )
import SPL.Compiler.Common.Error ( definition, throwErr )
import SPL.Compiler.Common.Misc
    ( wrapStateT, impossible, inSandboxedState )
import qualified SPL.Compiler.Parser.AST as AST
import SPL.Compiler.SemanticAnalysis.Core
    ( Field,
      OpBin(Cons, Plus, Minus, Mul, Div, Mod, Pow, LogAnd, LogOr),
      OpUnary(UnMinus, UnNeg),
      CoreType(CoreCharType, CoreTupleType, CoreIntType, CoreListType,
               CoreFunType, CoreBoolType, CoreVoidType),
      CoreExpr(..),
      CoreStmt(..),
      Offset,
      CoreFunCall(CoreFunCall),
      CoreFunBody(..),
      CoreIdentifier(CoreIdentifier),
      CoreVarDecl(CoreVarDecl),
      CoreFunDecl(CoreFunDecl),
      Core(..),
      TCMonad,
      TypeEnv(TypeEnv),
      Scope(GlobalVar, GlobalFun, Local),
      getEnv,
      getSubst,
      idName,
      varDeclType,
      funId, getLocalVarCounter )
import SPL.Compiler.SemanticAnalysis.CallGraphAnalysis (reorderAst)
import SPL.Compiler.SemanticAnalysis.Env (initGamma)
import SPL.Compiler.SemanticAnalysis.Unify
    ( generalise, liftToScheme, unify, Types(freeVars, ($*)) )
import SPL.Compiler.SemanticAnalysis.TypeCheckLib
    ( (<=*),
      addArgsToEnv,
      checkNotAssignToBuiltIn,
      addToEnv,
      addToEnvWithoutGen,
      adjustForMissingReturn,
      ast2coreType,
      freshVar,
      getFunRetType,
      instantiate,
      makeAbstractFunType,
      throwWarning,
      variableNotFoundErr )


typeCheckExpr :: AST.ASTExpr -> CoreType -> TCMonad CoreExpr
typeCheckExpr (AST.IntExpr loc i) tau = do
    let expectedType = CoreIntType loc
    unify expectedType tau
    return (IntExpr loc i)
typeCheckExpr (AST.CharExpr loc c) tau = do
    let expectedType = CoreCharType loc
    unify expectedType tau
    return (CharExpr loc c)
typeCheckExpr (AST.BoolExpr loc b) tau = do
    let expectedType = CoreBoolType loc
    unify expectedType tau
    return (BoolExpr loc b)
typeCheckExpr (AST.EmptyListExpr loc) tau = do
    expectedType <- CoreListType loc <$> freshVar loc "l"
    unify expectedType tau
    return (EmptyListExpr loc tau)
typeCheckExpr (AST.EmptyCharListExpr loc) tau = do
    let expectedType = CoreListType loc (CoreCharType loc)
    unify expectedType tau
    return (EmptyListExpr loc tau)
typeCheckExpr (AST.IdentifierExpr id) tau = do
    (id', scheme) <- typeCheckVar id tau
    case scheme of
        GlobalFun -> return (FunIdentifierExpr tau id')
        _ -> return (VarIdentifierExpr id')
typeCheckExpr (AST.FunCallExpr f) tau = do
    f' <- typeCheckFunCall f tau
    return $ FunCallExpr f'
typeCheckExpr (AST.TupExpr loc e1 e2) tau = do
    t1 <- freshVar (getLoc e1) "t1"
    e1' <- typeCheckExpr e1 t1
    t2 <- freshVar (getLoc e2) "t2"
    e2' <- typeCheckExpr e2 t2
    let expectedType = CoreTupleType loc t1 t2
    unify expectedType tau
    return $ TupExpr loc e1' e2'
typeCheckExpr (AST.FieldSelectExpr loc e []) tau = typeCheckExpr e tau
typeCheckExpr (AST.FieldSelectExpr loc e fields) tau = do
    FunCallExpr <$> typeCheckFunCall (
        (\(AST.FunCallExpr fc) -> fc) $
            foldl (\fcall field ->
                let floc = getLoc field
                in AST.FunCallExpr $ AST.ASTFunCall
                    floc
                    (AST.IdentifierExpr (AST.ASTIdentifier floc (T.pack $ show field)))
                    [fcall]
            ) e fields
        ) tau
typeCheckExpr (AST.OpExpr loc UnNeg e1) tau = do
    e1' <- typeCheckExpr e1 (CoreBoolType loc)
    let expectedType = CoreBoolType loc
    unify expectedType tau
    return $ OpExpr loc UnNeg e1'
typeCheckExpr (AST.OpExpr loc UnMinus e1) tau = do
    e1' <- typeCheckExpr e1 (CoreIntType loc)
    let expectedType = CoreIntType loc
    unify expectedType tau
    return $ OpExpr loc UnMinus e1'
typeCheckExpr e@(AST.Op2Expr loc e1 op e2) tau =
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
            let e1T = CoreIntType (getLoc e1)
                e2T = CoreIntType (getLoc e2)
            e1' <- typeCheckExpr e1 e1T
            e2' <- typeCheckExpr e2 e2T
            let expectedType = CoreIntType loc
            unify expectedType tau
            return $ Op2Expr loc e1' e1T op e2' e2T

        handleBoolOp = do
            let e1T = CoreBoolType (getLoc e1)
                e2T = CoreBoolType (getLoc e2)
            e1' <- typeCheckExpr e1 e1T
            e2' <- typeCheckExpr e2 e2T
            let expectedType = CoreBoolType loc
            unify expectedType tau
            return $ Op2Expr loc e1' e1T op e2' e2T

        handleConsOp = do
            c <- freshVar (getLoc e1) "c"
            e1' <- typeCheckExpr e1 c

            let e2T = CoreListType (getLoc e2) c
            e2' <- typeCheckExpr e2 e2T

            let expectedType = CoreListType (getLoc e) c
            unify expectedType tau
            return $ Op2Expr loc e1' c op e2' e2T

        handleOverloadedOp = do
            o <- freshVar (getLoc e1) "o"
            e1' <- typeCheckExpr e1 o
            e2' <- typeCheckExpr e2 o
            let expectedType = CoreBoolType loc
            unify expectedType tau

            pure $ Op2Expr loc e1' o op e2' o

typeCheckVar :: AST.ASTIdentifier -> CoreType -> TCMonad (CoreIdentifier, Scope)
typeCheckVar (AST.ASTIdentifier l idName) tau = do
    (TypeEnv env) <- use getEnv
    let value = M.lookup idName env

    case value of
        Just (scope, sch) -> do
            (instScheme, _) <- instantiate sch
            unify instScheme tau
            return (CoreIdentifier l idName, scope)
        Nothing -> variableNotFoundErr (CoreIdentifier l idName)

typeCheckFunCall :: AST.ASTFunCall -> CoreType -> TCMonad CoreFunCall
typeCheckFunCall (AST.ASTFunCall loc e args) tau = do
    (args', argTypes) <- unzip <$> mapM typeCheckArg args

    a <- freshVar loc "a"
    e' <- typeCheckExpr e a

    let expectedFunType =
            case argTypes of
                [] -> CoreFunType loc Nothing tau
                _  -> foldr (CoreFunType loc) tau (Just <$> argTypes)
    unify a expectedFunType

    return $ CoreFunCall loc e' expectedFunType args'

    where
        typeCheckArg :: AST.ASTExpr -> TCMonad (CoreExpr, CoreType)
        typeCheckArg arg = do
            argT <- freshVar (getLoc arg) "a"
            arg' <- typeCheckExpr arg argT
            return (arg', argT)

typeCheckFieldSelector :: AST.ASTIdentifier -> [Field] -> CoreType -> TCMonad CoreIdentifier
typeCheckFieldSelector id fields tau = do
    varT <- freshVar (getLoc id) "f"
    (id', _) <- typeCheckVar id varT
    actualType <- foldM typeCheckFields varT fields
    unify tau actualType
    return id'

    where
        toVar :: Field -> AST.ASTIdentifier
        toVar fd = AST.ASTIdentifier (getLoc fd) (T.pack $ show fd)

        typeCheckFields :: CoreType -> Field -> TCMonad CoreType
        typeCheckFields argType field = do
            expectedType <- freshVar (getLoc id) "f"
            typeCheckVar (toVar field) expectedType

            resultType <- freshVar (getLoc id) "f"
            let actualType = CoreFunType (getLoc field) (Just argType) resultType

            unify expectedType actualType
            return resultType

typeCheckStmt :: AST.ASTStmt -> CoreType -> TCMonad CoreStmt
typeCheckStmt (AST.IfElseStmt loc cond thenStmts elseStmts) tau = do
    cond' <- typeCheckExpr cond (CoreBoolType (getLoc cond))
    counter <- use getLocalVarCounter
    thenStmts' <- inSandboxedState getLocalVarCounter counter $ 
                  mapM (`typeCheckStmt` tau) thenStmts
    elseStmts' <- inSandboxedState getLocalVarCounter counter $ 
                  mapM (`typeCheckStmt` tau) elseStmts
    return $ IfElseStmt loc cond' thenStmts' elseStmts'

typeCheckStmt (AST.WhileStmt loc cond bodyStmts) tau = do
    cond' <- typeCheckExpr cond (CoreBoolType (getLoc cond))
    counter <- use getLocalVarCounter
    bodyStmts' <- inSandboxedState getLocalVarCounter counter $ 
                  mapM (`typeCheckStmt` tau) bodyStmts
    return $ WhileStmt loc cond' bodyStmts'

typeCheckStmt (AST.VarDeclStmt varDecl) _ = do
    varDecl'@(CoreVarDecl e t id' s) <- typeCheckVarDecl varDecl
    addToEnvWithoutGen Local id' t

    offset <- use getLocalVarCounter
    getLocalVarCounter += 1

    return $ VarDeclStmt offset varDecl'

typeCheckStmt (AST.AssignStmt loc id@(AST.ASTIdentifier idLoc idName) fields expr) tau = do
    resultT <- freshVar (getLoc id) "f"
    checkNotAssignToBuiltIn (CoreIdentifier idLoc idName)
    id' <- typeCheckFieldSelector id fields resultT
    expr' <- typeCheckExpr expr resultT
    return $ AssignStmt loc id' resultT fields expr'

typeCheckStmt (AST.ReturnStmt loc Nothing) tau = do
    unify (CoreVoidType loc) tau
    return (ReturnStmt loc Nothing)

typeCheckStmt (AST.ReturnStmt loc (Just expr)) tau = do
    returnT <- freshVar loc "r"
    expr' <- typeCheckExpr expr returnT
    unify returnT tau
    return $ ReturnStmt loc (Just expr')

typeCheckStmt (AST.FunCallStmt funCall) tau = do
    resultT <- freshVar (getLoc funCall) "f"
    funCall' <- typeCheckFunCall funCall resultT
    return $ FunCallStmt funCall'

typeCheckVarDecl :: AST.ASTVarDecl -> TCMonad CoreVarDecl
typeCheckVarDecl (AST.ASTVarDecl loc tau (AST.ASTIdentifier l i) e) = do
    varT <- freshVar loc "v"
    e' <- typeCheckExpr e varT
    case ast2coreType tau of
        Nothing -> -- use of Var keyword
            return $ CoreVarDecl loc varT (CoreIdentifier l i) e'
        Just expectedType -> do
            scheme <- generalise varT
            expectedType <=* scheme
            return $ CoreVarDecl loc varT (CoreIdentifier l i) e'


typeCheckFunDecl :: AST.ASTFunDecl -> CoreType -> TCMonad CoreFunDecl
typeCheckFunDecl f@(AST.ASTFunDecl loc id@(AST.ASTIdentifier idLoc "main") args tau body) abstractType = do
    let expectedType = CoreFunType (getLoc abstractType)
                                   Nothing
                                   (CoreVoidType . getLoc . getFunRetType $ abstractType)
    unify expectedType abstractType

    body' <- do { b <- typeCheckFunBody body (getFunRetType expectedType);
                       adjustForMissingReturn expectedType b }

    case ast2coreType tau of
        Nothing -> pure ()
        Just userType -> unify expectedType userType

    return $ CoreFunDecl loc (CoreIdentifier idLoc "main")
                             args'
                             expectedType
                             body'

    where
        args' = map (\(AST.ASTIdentifier l nm) -> CoreIdentifier l nm) args

typeCheckFunDecl f@(AST.ASTFunDecl loc id@(AST.ASTIdentifier idLoc idName) args tau body) abstractType = do
    initEnv <- (\(TypeEnv env) -> TypeEnv (M.delete idName env)) <$> use getEnv

    addArgsToEnv (getArgTypes abstractType args')

    body' <- do { b <- typeCheckFunBody body (getFunRetType abstractType);
                  adjustForMissingReturn abstractType b }

    case ast2coreType tau of
        Nothing -> pure ()
        Just expectedType -> do
            inSandboxedState getEnv initEnv
                       (do { funScheme <- generalise abstractType;
                             expectedType <=* funScheme } )

    return $ CoreFunDecl loc (CoreIdentifier idLoc idName)
                             args'
                             abstractType
                             body'

    where
        args' = map (\(AST.ASTIdentifier l nm) -> CoreIdentifier l nm) args
        getArgTypes _ [] = []
        getArgTypes (CoreFunType l (Just a) r) (x:xs) = (a,x) : getArgTypes r xs
        getArgTypes _ _ = impossible

sandBoxedTypeCheckFun :: AST.ASTFunDecl -> CoreType -> TCMonad CoreFunDecl
sandBoxedTypeCheckFun fun funType = do
    envBefore <- use getEnv
    getLocalVarCounter .= 0
    fun' <- typeCheckFunDecl fun funType
    getEnv .= envBefore
    pure fun'

typeCheckFunDecls :: SCC AST.ASTFunDecl -> TCMonad (SCC CoreFunDecl)
typeCheckFunDecls (AcyclicSCC func) = do
    funType <- makeAbstractFunType func
    func'@(CoreFunDecl _ _ _ t _ ) <- sandBoxedTypeCheckFun func funType

    scheme <- generalise t
    addToEnv GlobalFun (func' ^. funId) scheme
    pure (AcyclicSCC func')

typeCheckFunDecls (CyclicSCC funcs) = do
    initEnv <- use getEnv

    funTypes <- mapM makeAbstractFunType funcs
    mapM_ (uncurry (addToEnvWithoutGen GlobalFun)) $ zip (map toIdentifier funcs) funTypes

    funcs' <- zipWithM sandBoxedTypeCheckFun funcs funTypes

    CyclicSCC <$> forM funcs' (
        \f@(CoreFunDecl _ id _ t _) -> do
            scheme <- generalise t
            addToEnv GlobalFun id scheme
            pure f)

    where
        toIdentifier :: AST.ASTFunDecl -> CoreIdentifier
        toIdentifier (AST.ASTFunDecl _ (AST.ASTIdentifier l id) _ _ _) = CoreIdentifier l id


typeCheckFunBody :: AST.ASTFunBody -> CoreType -> TCMonad CoreFunBody
typeCheckFunBody (AST.ASTFunBody loc stmts) tau = do
    stmts' <- mapM (`typeCheckStmt` tau) stmts
    return $ CoreFunBody loc stmts'

typeCheckGlobVarDecl :: AST.ASTVarDecl -> TCMonad CoreVarDecl
typeCheckGlobVarDecl v@(AST.ASTVarDecl _ _ (AST.ASTIdentifier l id) _)  = do
    varDecl'@(CoreVarDecl _ t id' _) <- typeCheckVarDecl v
    addToEnvWithoutGen GlobalVar id' t
    return varDecl'

typeCheckToCore :: AST.AST -> TCMonad Core
typeCheckToCore ast = do
    let (AST.ASTOrdered varDecls funDecls) = reorderAst ast
    getEnv .= initGamma
    varDecls' <- mapM typeCheckGlobVarDecl varDecls
    funDecls' <- mapM typeCheckFunDecls funDecls

    subst <- use getSubst
    let tct' = Core (subst $* varDecls') (map (fmap (subst $*)) funDecls')

    sanityCheck tct'
    pure tct'

sanityCheck :: Core -> TCMonad ()
sanityCheck (Core varDecls funDecls) = do
    forM_ varDecls $ \varDecl -> do
        let t = varDecl ^. varDeclType
            ftv = freeVars t
        unless (S.null ftv) $
            definition (
                "Ambigous type variables " <>
                "[" <> T.intercalate ", " (S.toList ftv) <> "] " <>
                "found in type " <> T.pack (show t) <> ":") t
            >>= throwErr

    unless hasMain $
        throwWarning "No 'main' function found. Program will not execute"

    where
        hasMain = "main" `elem` map (^. traversed.funId.idName) funDecls
