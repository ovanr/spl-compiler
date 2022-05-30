{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.SemanticAnalysis.TypeCheck.TCon where

import SPL.Compiler.Common.Error
import Data.Maybe (fromMaybe)
import Control.Lens
import Control.Monad.State
import Data.Hashable
import Data.Set (Set)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Set.Ordered as SO
import Data.Foldable (toList)

import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import SPL.Compiler.SemanticAnalysis.CoreEntityLocation
import Control.Monad.Extra (unlessM)
import Debug.Trace

getTCon :: CoreType -> [TCon]
getTCon (CoreFunType _ x _ _) = x
getTCon _ = []

getFreeTCons :: Set TypeVar -> [TCon] -> [TCon]
getFreeTCons freeTV = filter (not . S.null . S.intersection freeTV . freeVars . unTCon)

updateTCon :: [TCon] -> CoreType -> CoreType
updateTCon tcons (CoreFunType loc _ as r) = CoreFunType loc tcons as r
updateTCon _ t = t

sanityCheckTCon :: TCon -> TCMonad ()
sanityCheckTCon tcon = do 
    subst <- use getSubst 
    sanityCheckTCon' (subst $* tcon)

    where
        sanityCheckTCon' t@(TEq CoreFunType{}) = tconError t >>= tcError
        sanityCheckTCon' t@(TOrd CoreFunType{}) = tconError t >>= tcError
        sanityCheckTCon' t@(TPrint CoreFunType{}) = tconError t >>= tcError
        sanityCheckTCon' _ = pure ()

ambiguousTConCheck :: TypeEnv -> CoreType -> TCon -> TCMonad ()
ambiguousTConCheck env t tcon = do
    subst <- use getSubst
    let freeTV = freeVars (subst $* t) <> freeVars env
    
    unless (all (`S.member` freeTV) $ freeVars tcon) $
        tconError tcon >>= tcError


isConcreteTCon :: TCon -> Bool
isConcreteTCon (TEq t) = isConcreteType t
isConcreteTCon (TOrd t) = isConcreteType t
isConcreteTCon (TPrint t) = isConcreteType t

mkTConFunDecl :: TCon -> CoreFunDecl
mkTConFunDecl tcon@(TEq t) =
    let funName = CoreIdentifier mempty $ "_eq_" <> T.pack (show $ hash tcon)
        funType = CoreFunType mempty [] [t, t] (CoreBoolType mempty)
        args = [CoreIdentifier mempty "x", CoreIdentifier mempty "y"]
    in CoreFunDecl mempty funName args funType (CoreFunBody mempty [] [])

mkTConFunDecl tcon@(TOrd t) =
    let funName = CoreIdentifier mempty $ "_ord_" <> T.pack (show $ hash tcon)
        funType = CoreFunType mempty [] [t, t] (CoreBoolType mempty)
        args = [CoreIdentifier mempty "x", CoreIdentifier mempty "y"]
    in CoreFunDecl mempty funName args funType (CoreFunBody mempty [] [])

mkTConFunDecl tcon@(TPrint t) =
    let funName = CoreIdentifier mempty $ "_print_" <> T.pack (show $ hash tcon)
        funType = CoreFunType mempty [] [t] (CoreVoidType mempty)
        args = [CoreIdentifier mempty "x"]
    in CoreFunDecl mempty funName args funType (CoreFunBody mempty [] [])

tconError :: TCon -> TCMonad Error
tconError tcon = do
    let header = T.pack $ "Unable to find an instance for " <> show tcon
    err <- definition (T.pack $ "'" <>
                       show tcon <>
                       "' instance has been inferred for: ") tcon
    return $ header : err

isFunctionOverloaded :: CoreFunDecl -> Bool
isFunctionOverloaded (CoreFunDecl _ _ _ t _) = not $ null (getTCon t)
