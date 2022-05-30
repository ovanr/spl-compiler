{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module SPL.Compiler.SemanticAnalysis.ConstantGlobalVar (
    globalVarConstantCheck 
    ) where

import Control.Monad.State
import Control.Monad.Except
import Data.Text (Text)
import Data.Either

import SPL.Compiler.Parser.AST
import SPL.Compiler.Parser.ASTEntityLocation
import SPL.Compiler.Common.Error

globalVarConstantCheck :: (MonadState s m, MonadError Error m, ContainsSource s) => AST -> m ()
globalVarConstantCheck (ASTUnordered leaves) = do
    mapM_ checkGlobalVarDecl (lefts leaves)
globalVarConstantCheck (ASTOrdered varDecls _) = do
    mapM_ checkGlobalVarDecl varDecls

checkGlobalVarDecl :: (MonadState s m, MonadError Error m, ContainsSource s) => ASTVarDecl -> m ()
checkGlobalVarDecl v@(ASTVarDecl _ _ _ e) = 
    unless (isExprConstant e) $
        mkError v

    where
        isExprConstant FunCallExpr{} = False 
        isExprConstant IdentifierExpr{} = False 
        isExprConstant (FieldSelectExpr _ e _) = isExprConstant e 
        isExprConstant (OpExpr _ _ e) = isExprConstant e 
        isExprConstant (Op2Expr _ e1 _ e2) = isExprConstant e1 && isExprConstant e2
        isExprConstant (TupExpr _ e1 e2) = isExprConstant e1 && isExprConstant e2 
        isExprConstant _ = True

mkError :: (MonadState s m, MonadError Error m, ContainsSource s) => ASTVarDecl -> m ()
mkError v@(ASTVarDecl _ _ (ASTIdentifier _ id) _) = do
    let header = [ "Global variables may only contain constant expressions" ]
    varDeclTrace <- definition ("In the definition of variable '" <> id <> "'") v
    throwError $ header <> varDeclTrace
