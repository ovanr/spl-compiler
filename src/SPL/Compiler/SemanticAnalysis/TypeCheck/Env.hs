{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module SPL.Compiler.SemanticAnalysis.TypeCheck.Env where

import Data.Text (Text)
import Data.Map (Map)
import Data.Set (Set)
import Data.Bifunctor
import Data.Either.Extra (maybeToEither)
import qualified Data.Map as M
import qualified Data.Set as S

import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TypeCheck.TCon

defLoc = EntityLoc (0,0) (0,0)

printEnv :: (Text, Scheme)
printEnv = ("print", 
             let var = TCTVarType defLoc mempty "a" 
             in Scheme (S.singleton "a") (TCTFunType defLoc (S.singleton $ TPrint var) 
                                                     var (TCTVoidType defLoc mempty)))

isEmptyEnv :: (Text, Scheme)
isEmptyEnv = ("isEmpty", 
             let listType = TCTListType defLoc mempty (TCTVarType defLoc mempty "a")
             in Scheme (S.singleton "a") (TCTFunType defLoc mempty
                                                     listType (TCTBoolType defLoc mempty)))
hdEnv :: (Text, Scheme)
hdEnv = ("hd", Scheme (S.singleton "a") 
                (TCTFunType defLoc mempty
                            (TCTListType defLoc mempty (TCTVarType defLoc mempty "a")) 
                            (TCTVarType defLoc mempty "a")))

tlEnv :: (Text, Scheme)
tlEnv = ("tl", Scheme (S.singleton "a") 
                   (TCTFunType defLoc mempty
                            (TCTListType defLoc mempty (TCTVarType defLoc mempty "a")) 
                            (TCTListType defLoc mempty (TCTVarType defLoc mempty "a")))) 

fstEnv :: (Text, Scheme)
fstEnv = ("fst", Scheme (S.fromList ["a", "b"]) 
                    (TCTFunType defLoc mempty 
                            (TCTTupleType defLoc mempty (TCTVarType defLoc mempty "a") (TCTVarType defLoc mempty "b")) 
                            (TCTVarType defLoc mempty "a"))) 

sndEnv :: (Text, Scheme)
sndEnv = ("snd", Scheme (S.fromList ["a", "b"]) 
                    (TCTFunType defLoc mempty 
                            (TCTTupleType defLoc mempty (TCTVarType defLoc mempty "a") (TCTVarType defLoc mempty "b")) 
                            (TCTVarType defLoc mempty "b"))) 

initGamma :: TypeEnv 
initGamma = TypeEnv . M.fromList . map (bimap (,Fun) (Global,)) $ [printEnv, isEmptyEnv, hdEnv, tlEnv, fstEnv, sndEnv]
