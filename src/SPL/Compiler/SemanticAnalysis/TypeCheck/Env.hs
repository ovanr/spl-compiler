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

unknownDef = EntityLoc (0,0) (0,0)

printEnv :: (Text, Scheme)
printEnv = ("print", 
             let var = TCTVarType unknownDef "a" 
             in Scheme (S.singleton "a") [TPrint var] 
                       (TCTFunType unknownDef var (TCTVoidType unknownDef)))

isEmptyEnv :: (Text, Scheme)
isEmptyEnv = ("isEmpty", 
             let listType = TCTListType unknownDef (TCTVarType unknownDef "a")
             in Scheme (S.singleton "a") [] 
                       (TCTFunType unknownDef listType (TCTBoolType unknownDef)))
hdEnv :: (Text, Scheme)
hdEnv = ("hd", Scheme (S.singleton "a") []
                (TCTFunType unknownDef 
                    (TCTListType unknownDef (TCTVarType unknownDef "a")) 
                    (TCTVarType unknownDef "a")))

tlEnv :: (Text, Scheme)
tlEnv = ("tl", Scheme (S.singleton "a") []
                   (TCTFunType unknownDef
                            (TCTListType unknownDef (TCTVarType unknownDef "a")) 
                            (TCTListType unknownDef (TCTVarType unknownDef "a")))) 

fstEnv :: (Text, Scheme)
fstEnv = ("fst", Scheme (S.fromList ["a", "b"]) []
                    (TCTFunType unknownDef 
                        (TCTTupleType unknownDef (TCTVarType unknownDef "a") (TCTVarType unknownDef "b"))
                        (TCTVarType unknownDef "a")))

sndEnv :: (Text, Scheme)
sndEnv = ("snd", Scheme (S.fromList ["a", "b"]) []
                    (TCTFunType unknownDef 
                        (TCTTupleType unknownDef (TCTVarType unknownDef "a") (TCTVarType unknownDef "b")) 
                        (TCTVarType unknownDef "b"))) 

initGamma :: TypeEnv 
initGamma = TypeEnv . M.fromList . map (bimap (,Fun) (Global,)) $ 
                [printEnv, isEmptyEnv, hdEnv, tlEnv, fstEnv, sndEnv]
