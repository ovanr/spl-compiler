{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.TypeChecker.TypeCheck where

import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import Data.Bifunctor
import Control.Monad.Random

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.Unify

newtype TCError e = TCError { msg :: e }

type RandErr e a = RandT StdGen (Either e) a

type Context = Map Text TCTType

tcFail e = lift (Left e)

freshVar :: MonadRandom m => EntityLoc -> m TCTType
freshVar loc = do
    prefix <- T.singleton <$> getRandomR ('a', 'z')
    suffix <- T.pack . show <$> getRandomR (10000 :: Int, 99999)
    return . TCTVarType loc $ prefix <> suffix

-- typeCheckVar :: Context ->
--                 TCTVarDecl ->
--                 RandErr (TCError [Text]) (TCTVarDecl, Subst)
-- typeCheckVar gamma (TCTVarDecl loc t (TCTIdentifier l i) e) = do
--     -- tau <- if 
--     (e', eSubst) <- typeCheckExpr gamma e tau
--     let tau' = substApply eSubst tau
--     tSubst <- lift (getMGTInstance t tau')
--     let subst = tSubst <> eSubst
--     return (TCTVarDecl loc t (TCTIdentifier l i) e', subst)


typeCheckExpr :: Context ->
                 TCTExpr ->
                 TCTType ->
                 RandErr (TCError [Text]) (TCTExpr, Subst)
typeCheckExpr gamma e@(IntExpr loc i) tau = do
    case tau of
        TCTVarType l alpha -> return (e, Subst $ M.fromList [(alpha, TCTIntType l)])
        TCTIntType l -> return (e, mempty)
        _ -> tcFail (TCError ["expected int type"])
typeCheckExpr _ _ _ = undefined

