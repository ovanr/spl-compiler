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
             let var = TCTVarType defLoc "a" 
             in Scheme (S.singleton "a") (TCTFunType defLoc (S.singleton $ TPrint var) 
                                                     var (TCTVoidType defLoc)))

hdEnv :: (Text, Scheme)
hdEnv = ("hd", Scheme (S.singleton "a") 
                (TCTFunType defLoc mempty
                            (TCTListType defLoc (TCTVarType defLoc "a")) 
                            (TCTVarType defLoc "a")))

tlEnv :: (Text, Scheme)
tlEnv = ("tl", Scheme (S.singleton "a") 
                   (TCTFunType defLoc mempty
                            (TCTListType defLoc (TCTVarType defLoc "a")) 
                            (TCTListType defLoc (TCTVarType defLoc "a")))) 

fstEnv :: (Text, Scheme)
fstEnv = ("fst", Scheme (S.fromList ["a", "b"]) 
                    (TCTFunType defLoc mempty 
                            (TCTTupleType defLoc (TCTVarType defLoc "a") (TCTVarType defLoc "b")) 
                            (TCTVarType defLoc "a"))) 

sndEnv :: (Text, Scheme)
sndEnv = ("snd", Scheme (S.fromList ["a", "b"]) 
                    (TCTFunType defLoc mempty 
                            (TCTTupleType defLoc (TCTVarType defLoc "a") (TCTVarType defLoc "b")) 
                            (TCTVarType defLoc "b"))) 

initGamma :: TypeEnv 
initGamma = TypeEnv . M.fromList . map (bimap (,Fun) (Global,)) $ [printEnv, hdEnv, tlEnv, fstEnv, sndEnv]
