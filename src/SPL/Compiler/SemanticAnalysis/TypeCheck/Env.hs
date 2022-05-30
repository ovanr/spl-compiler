{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module SPL.Compiler.SemanticAnalysis.TypeCheck.Env where

import Data.Text (Text)
import Data.Map (Map)
import Data.Bifunctor
import Data.Either.Extra (maybeToEither)
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.SemanticAnalysis.Core
import SPL.Compiler.SemanticAnalysis.TypeCheck.TCon


printEnv :: (Text, Scheme)
printEnv = ("print", 
             let var = CoreVarType mempty "a" 
             in Scheme (S.singleton "a")
                       (CoreFunType mempty [TPrint var] [var] (CoreVoidType mempty)))

isEmptyEnv :: (Text, Scheme)
isEmptyEnv = ("isEmpty", 
             let listType = CoreListType mempty (CoreVarType mempty "a")
             in Scheme (S.singleton "a") 
                       (CoreFunType mempty [] [listType] (CoreBoolType mempty)))
hdEnv :: (Text, Scheme)
hdEnv = ("hd", Scheme (S.singleton "a")
                (CoreFunType mempty []
                    [CoreListType mempty (CoreVarType mempty "a")]
                    (CoreVarType mempty "a")))

tlEnv :: (Text, Scheme)
tlEnv = ("tl", Scheme (S.singleton "a") 
                   (CoreFunType mempty []
                            [CoreListType mempty (CoreVarType mempty "a")]
                            (CoreListType mempty (CoreVarType mempty "a")))) 

fstEnv :: (Text, Scheme)
fstEnv = ("fst", Scheme (S.fromList ["a", "b"]) 
                    (CoreFunType mempty []
                        [CoreTupleType mempty (CoreVarType mempty "a") (CoreVarType mempty "b")]
                        (CoreVarType mempty "a")))

sndEnv :: (Text, Scheme)
sndEnv = ("snd", Scheme (S.fromList ["a", "b"]) 
                    (CoreFunType mempty []
                        [CoreTupleType mempty (CoreVarType mempty "a") (CoreVarType mempty "b")]
                        (CoreVarType mempty "b"))) 

initGamma :: TypeEnv 
initGamma = TypeEnv . M.fromList . map (second (GlobalFun,)) $ 
                [printEnv, isEmptyEnv, hdEnv, tlEnv, fstEnv, sndEnv]
