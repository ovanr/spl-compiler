{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module SPL.Compiler.SemanticAnalysis.TypeCheckLib where

import Data.Text (Text)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Set.Ordered as SO
import qualified Data.Text as T
import Data.Maybe
import Control.Monad.State
import Control.Lens

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error
import SPL.Compiler.Common.Misc (wrapStateT)
import qualified SPL.Compiler.Parser.AST as AST
import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.BindingTimeAnalysis (duplicateDefError)
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import Data.Foldable (toList)

ast2coreType :: AST.ASTType -> Maybe CoreType
ast2coreType (AST.ASTUnknownType loc) = Nothing
ast2coreType (AST.ASTFunType loc as r) = CoreFunType loc <$> mapM ast2coreType as <*> ast2coreType r
ast2coreType (AST.ASTTupleType loc tl tr) = CoreTupleType loc <$> ast2coreType tl <*> ast2coreType tr
ast2coreType (AST.ASTListType loc t) = CoreListType loc <$> ast2coreType t
ast2coreType (AST.ASTVarType loc t) = Just $ CoreVarType loc t
ast2coreType (AST.ASTIntType loc) = Just $ CoreIntType loc
ast2coreType (AST.ASTBoolType loc) = Just $ CoreBoolType loc
ast2coreType (AST.ASTCharType loc) = Just $ CoreCharType loc
ast2coreType (AST.ASTVoidType loc) = Just $ CoreVoidType loc

inSandboxState :: Lens' TypeCheckState a -> a -> TCMonad b -> TCMonad b
inSandboxState lens tcons = wrapStateT
                               (lens .~ tcons)
                               (\old new -> new & lens .~ (old ^. lens))

sanitize :: CoreType -> TCMonad (CoreType, Subst)
sanitize t = do
    scheme <- inSandboxState getEnv mempty (generalise t)
    instantiate scheme

instantiate :: Scheme -> TCMonad (CoreType, Subst)
instantiate (Scheme tv t) = do
    newNames <- mapM (\v -> (v,) <$> freshVar (getVarLoc v t) v) $ S.toList tv
    let subst = Subst . M.fromList $ newNames
    env <- use getEnv
    return (subst $* t, reverseSubst subst)

    where
        reverseSubst :: Subst -> Subst
        reverseSubst (Subst s) = Subst .
                                 M.fromList .
                                 map (\(k, CoreVarType l a) -> (a, CoreVarType l k)) .
                                 M.toList $ s
        
        getVarLoc :: TypeVar -> CoreType -> EntityLoc 
        getVarLoc v t = fromMaybe (getLoc t) (findLoc v t)

        findLoc :: TypeVar -> CoreType -> Maybe EntityLoc
        findLoc v1 (CoreVarType l v2)
            | v1 == v2 = Just l
            | otherwise = Nothing
        findLoc v1 (CoreListType _ t) = findLoc v1 t
        findLoc v1 (CoreTupleType _ t1 t2) =
            listToMaybe $ catMaybes [findLoc v1 t1, findLoc v1 t2]
        findLoc v1 (CoreFunType _ t1 t2) =
            listToMaybe . catMaybes $ map (findLoc v1) t1 ++ [findLoc v1 t2]
        findLoc _ _ = Nothing

freshVar :: EntityLoc -> Text -> TCMonad CoreType
freshVar loc prefix = do
    suffix <- T.pack . show <$> use getTvCounter
    getTvCounter += 1
    return $ CoreVarType loc (prefix <> suffix)

throwWarning :: Text -> TCMonad ()
throwWarning warn = getWarnings <>= [warn]

(<=*) :: CoreType -> Scheme -> TCMonad ()
(<=*) typ (Scheme tv coreType) = do
    subst <- use getSubst
    (typSanit, renameSubst) <- sanitize (subst $* typ)
    isInstanceOf renameSubst typSanit tv (subst $* coreType)

    where
        isInstanceOf :: Subst -> CoreType -> S.Set TypeVar -> CoreType -> TCMonad () 
        isInstanceOf _ CoreVoidType{} _ CoreVoidType{} = return ()
        isInstanceOf _ CoreIntType{}  _ CoreIntType{} = return ()
        isInstanceOf _ CoreCharType{} _ CoreCharType{} = return ()
        isInstanceOf _ CoreBoolType{} _ CoreBoolType{} = return ()
        isInstanceOf re v@(CoreVarType _ t) tv v2@(CoreVarType l a)
            | S.member a tv = addSubst a (setLoc l v)
            | not (S.member a tv) && a == t = return mempty
            | otherwise = typeMismatchError (re $* v2) (re $* v)

        isInstanceOf re t tv v2@(CoreVarType l a)
            | S.member a tv = addSubst a (setLoc l t)
            | S.null (freeVars t) = addSubst a (setLoc l t)
            | otherwise = typeMismatchError (re $* v2) (re $* t)

        isInstanceOf re (CoreListType _ t1) tv (CoreListType _ t2) =
           isInstanceOf re t1 tv t2

        isInstanceOf re (CoreTupleType _ a1 b1) tv (CoreTupleType _ a2 b2) = do
            isInstanceOf re a1 tv a2
            subst <- use getSubst
            isInstanceOf re b1 tv (subst $* b2)

        isInstanceOf re t1@(CoreFunType _ as1 _) tv t2@(CoreFunType _ as2 _) 
            | length as1 >= length as2 = do
                let (CoreFunType _ as1' r1) = curryAt (length as2) t1
                    (CoreFunType _ as2' r2) = curryAt (length as1) t2
                zipWithM_ (\a1 a2 -> do
                        subst <- use getSubst
                        isInstanceOf re a1 tv (subst $* a2)
                    ) as1' as2'
                subst <- use getSubst
                isInstanceOf re r1 tv (subst $* r2)

        isInstanceOf re t1 _ t2 = typeMismatchError (re $* t2) (re $* t1)

checkNotInGamma :: CoreIdentifier -> TCMonad ()
checkNotInGamma id@(CoreIdentifier l idName) = do
    TypeEnv env <- use getEnv
    when (M.member idName env) $
        duplicateDefError (AST.ASTIdentifier l idName)

variableNotFoundErr :: CoreIdentifier -> TCMonad a
variableNotFoundErr (CoreIdentifier l idName) = do
    varTrace <- definition (idName <> "' is accessed at:") l
    tcError $ ["Identifier not in scope: " <> idName] <> varTrace

makeAbstractFunType :: AST.ASTFunDecl -> TCMonad CoreType
makeAbstractFunType (AST.ASTFunDecl loc id@(AST.ASTIdentifier idLoc idName) args _ _) = do
    returnT <- freshVar idLoc "r"
    argTypes <- mapM (\(AST.ASTIdentifier l i) -> freshVar l "a") args
    return $ CoreFunType loc argTypes returnT

addToEnvWithoutGen :: Scope -> CoreIdentifier -> CoreType -> TCMonad ()
addToEnvWithoutGen scope id@(CoreIdentifier _ idName) idType = do
    checkNotInGamma id
    getEnv %= (\(TypeEnv env) -> TypeEnv $
                M.insert idName (scope, liftToScheme idType) env)

addToEnv :: Scope -> Text -> Scheme -> TCMonad ()
addToEnv scope id scheme = do
    TypeEnv env <- use getEnv
    getEnv %= \(TypeEnv env) -> TypeEnv $ M.insert id (scope, scheme) env

addArgsToEnv :: [(CoreType, CoreIdentifier)] -> TCMonad ()
addArgsToEnv args = do
    mapM_ (\(t, CoreIdentifier _ id) -> addToEnv Arg id (liftToScheme t)) args

adjustForMissingReturn :: CoreType -> CoreFunBody -> TCMonad CoreFunBody
adjustForMissingReturn t body@(CoreFunBody l varDecls stmts) =
    if not $ any isReturn stmts then do
        subst <- use getSubst
        let funType' = subst $* t
        let (CoreFunType _ _ retType) = funType'
        let (CoreVarType l' v) = retType
        addSubst v (CoreVoidType l')
        return $ CoreFunBody l varDecls (stmts ++ [ReturnStmt l Nothing])
    else
        pure body

    where
        isReturn :: CoreStmt -> Bool
        isReturn (IfElseStmt _ _ taken ntaken) = any isReturn (taken ++ ntaken)
        isReturn (WhileStmt _ _ taken) = any isReturn taken
        isReturn (ReturnStmt el _) = True
        isReturn _ = False
