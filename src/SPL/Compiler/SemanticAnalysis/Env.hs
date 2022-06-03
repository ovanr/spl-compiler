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

-- eqVoid :: (Text, Scheme)
-- eqVoid = ("_eq_void", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreVoidType mempty, CoreVoidType mempty] (CoreBoolType mempty)))

-- eqInt :: (Text, Scheme)
-- eqInt = ("_eq_int", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreIntType mempty, CoreIntType mempty] (CoreBoolType mempty)))

-- eqBool :: (Text, Scheme)
-- eqBool = ("_eq_bool", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreBoolType mempty, CoreBoolType mempty] (CoreBoolType mempty)))

-- eqChar :: (Text, Scheme)
-- eqChar = ("_eq_char", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreCharType mempty, CoreCharType mempty] (CoreBoolType mempty)))

-- eqList :: (Text, Scheme)
-- eqList = ("_eq_list", 
--             let argType1 = CoreFunType mempty [CoreVarType mempty "a", CoreVarType mempty "a"] (CoreBoolType mempty)
--                 argType2 = CoreListType mempty (CoreVarType mempty "a")
--             in Scheme (S.singleton "a") ([], CoreFunType mempty [argType1, argType2] (CoreBoolType mempty)))

-- eqTup :: (Text, Scheme)
-- eqTup = ("_eq_tup", 
--             let argType1 = CoreFunType mempty [CoreVarType mempty "a", CoreVarType mempty "a"] (CoreBoolType mempty)
--                 argType2 = CoreFunType mempty [CoreVarType mempty "b", CoreVarType mempty "b"] (CoreBoolType mempty)
--                 argType3 = CoreTupleType mempty (CoreVarType mempty "a") (CoreVarType mempty "b")
--             in Scheme (S.fromList ["a", "b"]) ([], CoreFunType mempty [argType1, argType2, argType3] (CoreBoolType mempty)))

-- ordVoid :: (Text, Scheme)
-- ordVoid = ("_ord_void", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreVoidType mempty, CoreVoidType mempty] (CoreBoolType mempty)))

-- ordInt :: (Text, Scheme)
-- ordInt = ("_ord_int", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreIntType mempty, CoreIntType mempty] (CoreBoolType mempty)))

-- ordBool :: (Text, Scheme)
-- ordBool = ("_ord_bool", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreBoolType mempty, CoreBoolType mempty] (CoreBoolType mempty)))

-- ordChar :: (Text, Scheme)
-- ordChar = ("_ord_char", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreCharType mempty, CoreCharType mempty] (CoreBoolType mempty)))

-- ordList :: (Text, Scheme)
-- ordList = ("_ord_list", 
--             let argType1 = CoreFunType mempty [CoreVarType mempty "a", CoreVarType mempty "a"] (CoreBoolType mempty)
--                 argType2 = CoreListType mempty (CoreVarType mempty "a")
--             in Scheme (S.singleton "a") ([], CoreFunType mempty [argType1, argType2] (CoreBoolType mempty)))

-- ordTup :: (Text, Scheme)
-- ordTup = ("_ord_tup", 
--             let argType1 = CoreFunType mempty [CoreVarType mempty "a", CoreVarType mempty "a"] (CoreBoolType mempty)
--                 argType2 = CoreFunType mempty [CoreVarType mempty "b", CoreVarType mempty "b"] (CoreBoolType mempty)
--                 argType3 = CoreTupleType mempty (CoreVarType mempty "a") (CoreVarType mempty "b")
--             in Scheme (S.fromList ["a", "b"]) ([], CoreFunType mempty [argType1, argType2, argType3] (CoreBoolType mempty)))

-- printVoid :: (Text, Scheme)
-- printVoid = ("_print_void", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreVoidType mempty] (CoreVoidType mempty)))

-- printInt :: (Text, Scheme)
-- printInt = ("_print_int", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreIntType mempty] (CoreVoidType mempty)))

-- printBool :: (Text, Scheme)
-- printBool = ("_print_bool", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreBoolType mempty] (CoreVoidType mempty)))

-- printChar :: (Text, Scheme)
-- printChar = ("_print_char", 
--              Scheme mempty 
--                        ([], CoreFunType mempty [CoreCharType mempty] (CoreVoidType mempty)))

-- printList :: (Text, Scheme)
-- printList = ("_print_list", 
--             let argType1 = CoreFunType mempty [CoreVarType mempty "a"] (CoreVoidType mempty)
--                 argType2 = CoreListType mempty (CoreVarType mempty "a")
--             in Scheme (S.singleton "a") ([], CoreFunType mempty [argType1, argType2] (CoreVoidType mempty)))

-- printTup :: (Text, Scheme)
-- printTup = ("_print_tup", 
--             let argType1 = CoreFunType mempty [CoreVarType mempty "a"] (CoreVoidType mempty)
--                 argType2 = CoreFunType mempty [CoreVarType mempty "b"] (CoreVoidType mempty)
--                 argType3 = CoreTupleType mempty (CoreVarType mempty "a") (CoreVarType mempty "b")
--             in Scheme (S.fromList ["a", "b"]) ([], CoreFunType mempty [argType1, argType2, argType3] (CoreVoidType mempty)))

builtIns :: [(Text,Scheme)]
builtIns = [print', isEmpty, hd', tl', fst', snd']

initGamma :: TypeEnv 
initGamma = TypeEnv . M.fromList . map (second (GlobalFun,)) $ builtIns
