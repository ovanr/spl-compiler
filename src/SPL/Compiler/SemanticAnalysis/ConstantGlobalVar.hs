{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module SPL.Compiler.SemanticAnalysis.ConstantGlobalVar (
    globalVarConstantCheck 
    ) where

import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TCTEntityLocation
import SPL.Compiler.Common.Error
import Control.Monad.State
import Control.Monad.Except

globalVarConstantCheck :: (MonadState s m, MonadError Error m, ContainsSource s) => TCT -> m ()
globalVarConstantCheck (TCT varDecls _) = do
    mapM_ checkGlobalVarDecl varDecls

checkGlobalVarDecl :: (MonadState s m, MonadError Error m, ContainsSource s) => TCTVarDecl -> m ()
checkGlobalVarDecl v@(TCTVarDecl _ _ _ e) = 
    unless (isExprConstant e) $
        mkError v

    where
        isExprConstant (FieldSelectExpr _) = False 
        isExprConstant (FunCallExpr _) = False 
        isExprConstant (OpExpr _ _ e) = isExprConstant e 
        isExprConstant (Op2Expr _ e1 _ e2) = isExprConstant e1 && isExprConstant e2
        isExprConstant _ = True

mkError :: (MonadState s m, MonadError Error m, ContainsSource s) => TCTVarDecl -> m ()
mkError v@(TCTVarDecl _ _ (TCTIdentifier _ id) _) = do
    let header = [ "Global variables may only contain constant expressions" ]
    varDeclTrace <- definition ("In the definition of variable '" <> id <> "'") v
    throwError $ header <> varDeclTrace

