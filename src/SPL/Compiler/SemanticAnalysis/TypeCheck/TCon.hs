{-# LANGUAGE TemplateHaskell #-}
module SPL.Compiler.SemanticAnalysis.TypeCheck.TCon where

import qualified Data.Map as M
import Data.Text (Text)
import Data.Graph
import Data.Map
import Control.Monad.State
import Control.Lens

import SPL.Compiler.SemanticAnalysis.Core hiding (getSourceCode, getSourcePath, _getSourcePath, _getSourceCode)
import SPL.Compiler.Common.Error
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify

data TConState = TConState {
    _env :: Map Text [TCon],
    _newTCon :: [TCon],
    _getSourcePath :: FilePath,
    _getSourceCode :: [Text]
}

makeLenses 'TConState

instance ContainsSource TConState where
    getFilePath = _getSourcePath
    getSource = _getSourceCode

type TConMonad a = StateT TConState (Either Error) a

genTConCore :: Core -> TConMonad Core
genTConCore (Core varDecls funDecls) = do 
    funDecls' <- mapM genTConFunDecls funDecls
    pure $ Core varDecls funDecls'

genTConFunDecls :: SCC CoreFunDecl -> TConMonad (SCC CoreFunDecl)
genTConFunDecls (AcyclicSCC fun) = _wb
genTConFunDecls (CyclicSCC funDecls) = _wc

-- genTConFunDecl :: CoreFunDecl -> TCMonad CoreFunDecl
-- genTConFunDecl (CoreFunDecl lf id args t (CoreFunBody lb vs sts)) = _wd

-- -- funTCons :: Text -> CoreType -> TCMonad [TCon]
-- -- funTCons id instanceT = do
-- --     TypeEnv env <- use getEnv
-- --     case M.lookup id env of
-- --         Nothing -> pure []
-- --         Just (_, Scheme _ generalT) -> do
-- --             unify instanceT (unwrap (length tcons) generalT)
-- --             subst <- use getSubst
-- --             pure (subst $* tcons)
            
-- --     where
-- --         unwrap 0 t = t
-- --         unwrap n (CoreFunType l _ r) = unwrap (n-1) r
-- --         unwrap n t = t

-- -- mkEqOrOrdType :: CoreType -> CoreType
-- -- mkEqOrOrdType t = CoreFunType mempty [t, t] (CoreBoolType mempty)

-- -- resolveTCons :: TCon -> (CoreExpr, CoreType) 
-- -- resolveTCons (TEq CoreVoidType{}) = do 
-- --     let funType = CoreFunType mempty [CoreVoidType mempty, CoreVoidType mempty] (CoreBoolType mempty)
-- --     (FunIdentifierExpr funType (CoreIdentifier mempty "_eq_void"), funType)
-- -- resolveTCons (TEq (CoreListType l t)) = do 
-- --     let funType = CoreFunType mempty [CoreVoidType mempty, CoreVoidType mempty] (CoreBoolType mempty)
-- --     (FunIdentifierExpr funType (CoreIdentifier mempty "_eq_void"), funType)

-- -- genTConExpr :: CoreExpr -> TCMonad CoreExpr
-- -- genTConExpr (FunCallExpr fc) = FunCallExpr <$> genTConFunCall fc
-- -- genTConExpr e@(FunIdentifierExpr typ (CoreIdentifier loc id)) = do
-- --     tcons <- funTCons id typ
-- --     (tConsArgs, tConsTypes) <- resolveTCons tcons
-- --     pure $ FunCallExpr (CoreFunCall loc e (updateType tConsTypes typ) tConsArgs)
-- -- genTConExpr (OpExpr loc op e) = OpExpr loc op <$> genTConExpr e
-- -- genTConExpr (Op2Expr loc e1 _ _ e2 _) = _ -- op2expr needs to store type of e1 and e2
-- -- genTConExpr (TupExpr loc e1 e2) = TupExpr loc <$> genTConExpr e1 <*> genTConExpr e2
-- -- genTConExpr e = pure e

-- genTConFunCall :: CoreFunCall -> TCMonad CoreFunCall
-- genTConFunCall (CoreFunCall loc e t args) = 
--     CoreFunCall loc <$> genTConExpr e <*> pure t <*> mapM genTConExpr args

-- genTConStmt :: CoreStmt -> TCMonad CoreStmt
-- genTConStmt (IfElseStmt loc e taken ntaken) = 
--     IfElseStmt loc <$> genTConExpr e <*> mapM genTConStmt taken <*> mapM genTConStmt ntaken
-- genTConStmt (WhileStmt loc e taken) =
--     WhileStmt loc <$> genTConExpr e <*> mapM genTConStmt taken
-- genTConStmt (AssignStmt loc id t fds e) = 
--     AssignStmt loc id t fds <$> genTConExpr e
-- genTConStmt (FunCallStmt funCall) =
--     FunCallStmt <$> genTConFunCall funCall 
-- genTConStmt stmt@(ReturnStmt _ Nothing) = pure stmt
-- genTConStmt stmt@(ReturnStmt loc (Just e)) =
--     ReturnStmt loc . Just <$> genTConExpr e
