{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module SPL.Compiler.SemanticAnalysis.Env where

import Data.Text (Text)
import Data.Map (Map)
import Data.Bifunctor
import Data.Either.Extra (maybeToEither)
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.SemanticAnalysis.Core

print' :: (Text, Scheme)
print' = ("print", 
             let var = CoreVarType mempty "a" 
             in Scheme (S.singleton "a")
                       (CoreFunType mempty (Just var) (CoreVoidType mempty)))

isEmpty :: (Text, Scheme)
isEmpty = ("isEmpty", 
             let listType = CoreListType mempty (CoreVarType mempty "a")
             in Scheme (S.singleton "a") 
                       (CoreFunType mempty (Just listType) (CoreBoolType mempty)))
hd' :: (Text, Scheme)
hd' = ("hd", Scheme (S.singleton "a")
                (CoreFunType mempty
                (Just $ CoreListType mempty (CoreVarType mempty "a"))
                (CoreVarType mempty "a")))

tl' :: (Text, Scheme)
tl' = ("tl", Scheme (S.singleton "a") 
                   (CoreFunType mempty
                   (Just $ CoreListType mempty (CoreVarType mempty "a"))
                   (CoreListType mempty (CoreVarType mempty "a")))) 

fst' :: (Text, Scheme)
fst' = ("fst", Scheme (S.fromList ["a", "b"]) 
                    (CoreFunType mempty
                    (Just $ CoreTupleType mempty (CoreVarType mempty "a") (CoreVarType mempty "b"))
                    (CoreVarType mempty "a")))

snd' :: (Text, Scheme)
snd' = ("snd", Scheme (S.fromList ["a", "b"]) 
                    (CoreFunType mempty
                    (Just $ CoreTupleType mempty (CoreVarType mempty "a") (CoreVarType mempty "b"))
                    (CoreVarType mempty "b")))

builtIns :: [(Text,Scheme)]
builtIns = [print', isEmpty, hd', tl', fst', snd']

initGamma :: TypeEnv 
initGamma = TypeEnv . M.fromList . map (second (GlobalFun,)) $ builtIns
