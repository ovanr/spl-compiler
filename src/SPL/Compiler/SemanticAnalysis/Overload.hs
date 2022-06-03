{-# LANGUAGE BangPatterns #-}
module SPL.Compiler.SemanticAnalysis.Overload where

import qualified Data.Map as M
import Data.Text (Text)
import Data.Graph
import Control.Monad.State.Strict
import Control.Lens

import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.TypeCheckLib (getTVarLoc)
import SPL.Compiler.SemanticAnalysis.OverloadLib
import SPL.Compiler.Common.Error
import SPL.Compiler.Common.Misc (impossible)
import SPL.Compiler.SemanticAnalysis.Unify
import Data.Tuple.Extra ((&&&))
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.Set as S
import SPL.Compiler.Common.EntityLocation
import Data.Foldable (fold)

resolveOverloading :: Core -> TConMonad Core
resolveOverloading (Core varDecls funDecls) = do
    funDecls' <- mapM rewriteTConFunDecls funDecls
    pure $ Core varDecls funDecls'

rewriteTConFunDecls :: SCC CoreFunDecl -> TConMonad (SCC CoreFunDecl)
rewriteTConFunDecls (AcyclicSCC fun@(CoreFunDecl _ (CoreIdentifier _ id) _ t _)) = do
    gatherTConFunDecl fun
    tcons <- S.toList <$> use newTCon
    mapM_ (ambiguousTConCheck t) tcons
    env %= M.insert id (tcons,t)
    AcyclicSCC <$> rewriteTConFunDecl fun
rewriteTConFunDecls (CyclicSCC funDecls) = do
    findFixPoint (gatherTCon funDecls)
    env' <- use env
    CyclicSCC <$> forM funDecls rewriteTConFunDecl

    where
        gatherTCon :: [CoreFunDecl] -> TConMonad Int
        gatherTCon funcs = do 
            sum <$> forM funcs (\f@(CoreFunDecl _ (CoreIdentifier _ id) _ t _) -> do
                gatherTConFunDecl f
                tcons <- S.toList <$> use newTCon
                mapM_ (ambiguousTConCheck t) tcons
                env %= M.insert id (tcons,t)
                pure $ length tcons)
        findFixPoint :: Monad m => m Int -> m Int
        findFixPoint m = do
            i1 <- m
            i2 <- m
            if i1 == i2 then
                pure i1
            else
                findFixPoint m

rewriteTConFunDecl :: CoreFunDecl -> TConMonad CoreFunDecl
rewriteTConFunDecl (CoreFunDecl lf
                                ident@(CoreIdentifier _ name)
                                args
                                t@(CoreFunType lt argT retT)
                                (CoreFunBody lb varDecls stmts)) = do
    tcons <- concat . maybeToList . fmap fst . M.lookup name <$> use env
    let extraArgs = map mkArg tcons
    tconArgs .= M.fromList (zip tcons extraArgs)

    varDecls' <- mapM rewriteTConVarDecl varDecls
    stmts' <- mapM rewriteTConStmt stmts

    let tconTypes = map mkTConVarType tcons

    pure $ CoreFunDecl lf
                       ident
                       (extraArgs ++ args)
                       (foldr (CoreFunType lf) retT (map Just tconTypes ++ [argT]))
                       (CoreFunBody lb varDecls' stmts')
rewriteTConFunDecl _ = impossible

rewriteTConVarDecl :: CoreVarDecl -> TConMonad CoreVarDecl
rewriteTConVarDecl (CoreVarDecl loc t id e) = CoreVarDecl loc t id <$> rewriteTConExpr e

rewriteTConStmt :: CoreStmt -> TConMonad CoreStmt
rewriteTConStmt (IfElseStmt loc e taken ntaken) =
    IfElseStmt loc <$> rewriteTConExpr e <*> mapM rewriteTConStmt taken <*> mapM rewriteTConStmt ntaken
rewriteTConStmt (WhileStmt loc e taken) =
    WhileStmt loc <$> rewriteTConExpr e <*> mapM rewriteTConStmt taken
rewriteTConStmt (AssignStmt loc id t fds e) = AssignStmt loc id t fds <$> rewriteTConExpr e
rewriteTConStmt (FunCallStmt funCall) = FunCallStmt <$> rewriteTConFunCall funCall
rewriteTConStmt stmt@(ReturnStmt _ Nothing) = pure stmt
rewriteTConStmt stmt@(ReturnStmt loc (Just e)) = ReturnStmt loc . Just <$> rewriteTConExpr e

getNeededTCons :: Text -> CoreType -> TConMonad [(TCon, CoreType)]
getNeededTCons funName instanceT = do
    env' <- use env
    case M.lookup funName env' of
        Nothing -> pure []
        Just (tcons, generalT) -> do
            let idSubst = mkIdentitySubst instanceT
            Subst subst <- (<> idSubst) <$> unify' generalT instanceT
            pure $ mapMaybe (sequence . (id &&& flip M.lookup subst . unTCon)) tcons

rewriteTConExpr :: CoreExpr -> TConMonad CoreExpr
rewriteTConExpr (FunCallExpr fc) = FunCallExpr <$> rewriteTConFunCall fc
rewriteTConExpr (TupExpr loc e1 e2) = TupExpr loc <$> rewriteTConExpr e1 <*> rewriteTConExpr e2
rewriteTConExpr (OpExpr loc op e) = OpExpr loc op <$> rewriteTConExpr e
rewriteTConExpr e@(FunIdentifierExpr typ (CoreIdentifier loc id)) = do
    neededTCons <- getNeededTCons id typ
    instances <- mapM mkTConArgExpr neededTCons
    pure $ case instances of
        [] -> e
        xs -> let funCallType = foldr (CoreFunType loc . (Just . snd)) typ instances
              in FunCallExpr $ CoreFunCall loc e funCallType (map fst instances)
rewriteTConExpr e@(Op2Expr loc e1 t1 op e2 t2) = do
    case op of
        Equal -> do
            e1' <- rewriteTConExpr e1
            e2' <- rewriteTConExpr e2
            (expr, typ) <- mkTConArgExpr (TEq loc mempty, t1)
            pure . FunCallExpr $ CoreFunCall loc expr typ [e1', e2']
        Less -> do
            e1' <- rewriteTConExpr e1
            e2' <- rewriteTConExpr e2
            (expr, typ) <- mkTConArgExpr (TOrd loc mempty, t1)
            pure . FunCallExpr $ CoreFunCall loc expr typ [e1', e2']
        Greater -> OpExpr loc UnNeg <$> rewriteTConExpr (Op2Expr loc e1 t1 LessEq e2 t2)
        LessEq -> do
            rewriteTConExpr $ 
                Op2Expr loc (Op2Expr loc e1 t1 Less e2 t2) 
                            (CoreBoolType loc)
                             LogOr
                            (Op2Expr loc e1 t1 Equal e2 t2) 
                            (CoreBoolType loc)
        GreaterEq -> OpExpr loc UnNeg <$> rewriteTConExpr (Op2Expr loc e1 t1 Less e2 t2)
        Nequal -> OpExpr loc UnNeg <$> rewriteTConExpr (Op2Expr loc e1 t1 Equal e2 t2)
        _ -> do
            e1' <- rewriteTConExpr e1
            e2' <- rewriteTConExpr e2
            pure $ Op2Expr loc e1' t1 op e2' t2
rewriteTConExpr e = pure e

rewriteTConFunCall :: CoreFunCall -> TConMonad CoreFunCall
rewriteTConFunCall (CoreFunCall loc e t args) =
    CoreFunCall loc <$> rewriteTConExpr e <*> pure t <*> mapM rewriteTConExpr args

gatherTConFunDecl :: CoreFunDecl -> TConMonad ()
gatherTConFunDecl (CoreFunDecl _ (CoreIdentifier _ id) _ _ (CoreFunBody _ varDecls stmts)) = do
    newTCon .= mempty
    mapM_ gatherTConVarDecl varDecls
    mapM_ gatherTConStmt stmts

gatherTConVarDecl :: CoreVarDecl -> TConMonad ()
gatherTConVarDecl (CoreVarDecl loc t id e) = gatherTConExpr e

mkIdentitySubst :: CoreType -> Subst
mkIdentitySubst t = 
    let tv = S.toList (freeVars t)
    in Subst . M.fromList $ map (\v -> (v, CoreVarType (getTVarLoc v t) v)) tv

gatherTConsFromFun :: Text -> CoreType -> TConMonad [TCon]
gatherTConsFromFun funName instanceT = do
    env' <- use env
    case M.lookup funName env' of
        Nothing -> pure []
        Just (tcons, generalT) -> do
            let idSubst = mkIdentitySubst instanceT
            subst <- unify' generalT instanceT
            pure $ concatMap (getFree (subst <> idSubst)) tcons

    where
        getFree :: Subst -> TCon -> [TCon]
        getFree (Subst s) tcon =
            case M.lookup (unTCon tcon) s of
                Nothing -> []
                Just typ -> map (constructTConFrom tcon (getLoc instanceT)) . S.toList $ freeVars typ

addTConToEnv :: [TCon] -> TConMonad ()
addTConToEnv xs = do
    newTCon %= S.union (S.fromList xs)

gatherTConExpr :: CoreExpr -> TConMonad ()
gatherTConExpr (FunCallExpr fc) = gatherTConFunCall fc
gatherTConExpr (TupExpr loc e1 e2) = gatherTConExpr e1 >> gatherTConExpr e2
gatherTConExpr (OpExpr loc op e) = gatherTConExpr e
gatherTConExpr e@(FunIdentifierExpr typ (CoreIdentifier loc id)) = do
    gatherTConsFromFun id typ >>= addTConToEnv
gatherTConExpr (Op2Expr loc e1 t1 op e2 t2) = do
    gatherTConExpr e1
    gatherTConExpr e2
    let freeTV = S.toList $ freeVars t1
    case op of
        Equal -> addTConToEnv $ map (TEq loc) freeTV
        Less -> addTConToEnv $ map (TOrd loc) freeTV
        Greater -> addTConToEnv $ map (TEq loc)  freeTV
        LessEq -> addTConToEnv $ concatMap (\tv -> [TEq loc tv, TOrd loc tv]) freeTV
        GreaterEq -> addTConToEnv $ concatMap (\tv -> [TEq loc tv, TOrd loc tv]) freeTV
        Nequal -> addTConToEnv $ map (TEq loc) freeTV
        _ -> pure ()
gatherTConExpr e = pure ()

gatherTConFunCall :: CoreFunCall -> TConMonad ()
gatherTConFunCall (CoreFunCall loc e t args) =
    gatherTConExpr e >> mapM_ gatherTConExpr args

gatherTConStmt :: CoreStmt -> TConMonad ()
gatherTConStmt (IfElseStmt loc e taken ntaken) =
    gatherTConExpr e >> mapM_ gatherTConStmt taken >> mapM_ gatherTConStmt ntaken
gatherTConStmt (WhileStmt loc e taken) =
    gatherTConExpr e >> mapM_ gatherTConStmt taken
gatherTConStmt (AssignStmt loc id t fds e) = gatherTConExpr e
gatherTConStmt (FunCallStmt funCall) = gatherTConFunCall funCall
gatherTConStmt stmt@(ReturnStmt _ Nothing) = pure ()
gatherTConStmt stmt@(ReturnStmt loc (Just e)) = gatherTConExpr e
