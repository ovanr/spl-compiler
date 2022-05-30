module SPL.Compiler.SemanticAnalysis.TypeCheck.TCon where

import SPL.Compiler.SemanticAnalysis.Core
import Data.Set (Set)

getTCon :: CoreType -> [TCon]

getFreeTCons :: Set TypeVar -> [TCon] -> [TCon] 

updateTCon :: [TCon] -> CoreType -> CoreType

isConcreteTCon :: TCon -> Bool

mkTConFunDecl :: TCon -> CoreFunDecl

tconError :: TCon -> TCMonad Error

isFunctionOverloaded :: CoreFunDecl -> Bool
