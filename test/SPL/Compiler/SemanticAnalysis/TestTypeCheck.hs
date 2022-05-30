{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# LANGUAGE TypeOperators #-}

module SPL.Compiler.SemanticAnalysis.TestTypeCheck (htf_thisModulesTests) where

import Test.Framework hiding (Fun(..))
import Control.Monad
import Data.Default
import Data.Tuple
import Data.Bifunctor
import Data.Text (Text)
import Data.Set (Set)
import Control.Lens
import Control.Monad.State
import Data.Foldable (fold)
import qualified Data.Set as S
import qualified Data.Map as M

import SPL.Compiler.Common.Testable
import SPL.Compiler.SemanticAnalysis.Testable
import SPL.Compiler.SemanticAnalysis.Core
import qualified SPL.Compiler.Parser.AST as AST
import SPL.Compiler.SemanticAnalysis.TypeCheck.TCon
import SPL.Compiler.SemanticAnalysis.TypeCheck.Env (initGamma)
import SPL.Compiler.SemanticAnalysis.TypeCheck
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import SPL.Compiler.SemanticAnalysis.TypeProperty
import Data.Functor (($>))
import SPL.Compiler.CodeGen.IRLang (type (-->))
import Data.Graph (SCC(..))

type TypeCheckTest a = ((a, CoreType), Maybe (CoreType, [TCon])) 
type TypeCheckTestEnv a = ((TypeEnv, a, CoreType), Maybe (CoreType, [TCon]))

forall :: [Text] -> CoreType -> Scheme
forall vars = Scheme (S.fromList vars)

-- Shorthand operators to create a type check tests

infixl 2 ~=
(~=) :: (a, CoreType) -> (CoreType, [TCon]) -> TypeCheckTest a
(a, t) ~= (typ, tcon) = ((a, t), Just (typ,tcon))

infixl 2 ~\=
(~\=) :: a -> CoreType -> TypeCheckTest a
a ~\= t = ((a, t), Nothing)

infixl 2 .::
(.::) :: AST.ASTFunDecl -> (CoreType, [TCon]) -> TypeCheckTest AST.ASTFunDecl
f@(AST.ASTFunDecl{}) .:: (typ,tcon) = ((f, typ), Just (typ, tcon))

failure :: AST.ASTFunDecl -> CoreType -> TypeCheckTest AST.ASTFunDecl
failure f@(AST.ASTFunDecl _ _ _ _ _) tau = ((f, tau), Nothing)

infixl 2 =:: 
(=::) :: (Text, CoreType, [TCon]) -> AST.ASTExpr -> TypeCheckTest AST.ASTVarDecl
(=::) (id, t, tcon) e = 
    ((AST.ASTVarDecl def (AST.ASTUnknownType def) (AST.ASTIdentifier def id) e, t), Just (t, tcon))

infixl 2 =\:
(=\:) :: (Text, CoreType) -> AST.ASTExpr -> TypeCheckTest AST.ASTVarDecl
(=\:) (id, t) e  = 
    ((AST.ASTVarDecl def (AST.ASTUnknownType def) (AST.ASTIdentifier def id) e, t), Nothing)

infixl 1 |= 
(|=) :: [(Text, Scope, Scheme)] -> TypeCheckTest a -> TypeCheckTestEnv a
(|=) env ((a, t), r) = 
    ((TypeEnv . M.fromList . map (\(a,b,c) -> (a,(b,c))) $ env, a, t), r)

thd3 :: (a,b,c) -> c
thd3 (_,_,x) = x

snd3 :: (a,b,c) -> b
snd3 (_,x,_) = x

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

executeCoreTests :: (Show a, Show b) => [TypeCheckTestEnv a] ->
                  (a -> CoreType -> TCMonad (b, CoreType)) ->
                  IO ()
executeCoreTests tests evaluator =
    forM_ tests $ \((gamma, a, initialTyp), expected) -> do
        let state = TypeCheckState 0 mempty mempty mempty mempty mempty mempty
        let actual = runStateT (getEnv .= (initGamma <> gamma) >> evaluator a initialTyp) state
        case expected of
            Just (expectedTyp, expectedTCon) ->
                case actual of
                    Right ((_, actualTyp), TypeCheckState _ actualSubst _ actualTCon _ _ _)  -> do 
                        -- compare up types up to alpha eq
                        assertEqual expectedTyp (toTestForm (actualSubst $* actualTyp))
                        -- compare type constraints via strict eq
                        let renameSubst = matchVars expectedTyp (actualSubst $* actualTyp)
                        mapM_ (\con -> assertElem con $ S.toList (actualSubst $* actualTCon)) 
                              (renameSubst <> actualSubst $* expectedTCon)

                    Left err -> assertFailure $ "expected substitution but got failure: " <> show err

            Nothing -> print actual >> void (assertLeft actual)

matchVars :: CoreType -> CoreType -> Subst
matchVars (CoreVarType _ a) v = Subst $ M.singleton a v
matchVars (CoreListType _ t1) (CoreListType _ t2) = matchVars t1 t2
matchVars (CoreTupleType _ a1 b1) (CoreTupleType _ a2 b2) = matchVars b1 b2 <> matchVars a1 a2 
matchVars (CoreFunType _ _ a1 b1) (CoreFunType _ _ a2 b2) = fold (zipWith matchVars a1 a2) <> matchVars b1 b2 
matchVars _ _ = mempty

typeCheckExpr' a t = (\a -> (a,t)) <$> typeCheckExpr a t

test_type_check_field_selector_1 = do
            -- x :: [Int] |- x.hd : Int = 
            let test = [("x", Local, forall ["a"] (typ @[Int]))] |=
                        (fd "x" [Hd def], typ @(TVar "sigma")) ~= (typ @Int, [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_field_selector_2 = do
            -- x :: [Int] |- x.tl : [Int] = 
            let test = [("x", Local, forall ["a"] (typ @[Int]))] |=
                        (fd "x" [Tl def], typ @(TVar "sigma")) ~= (typ @[Int], [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_field_selector_3 = do
            -- x :: [Int] |- x.tl.hd : Int = 
            let test = [("x", Local, forall ["a"] (typ @[Int]))] |=
                        (fd "x" [Tl def, Hd def], typ @(TVar "sigma")) ~= (typ @Int, [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_field_selector_4 = do
            -- x :: ([Int], a) |- x.fst.tl.hd : Int = 
            let test = [("x", Local, forall ["a"] (typ @([Int], TVar "a")))] |=
                        (fd "x" [Fst def, Tl def, Hd def], typ @(TVar "sigma")) ~= (typ @Int, [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_field_selector_5 = do
            -- x :: (a, [(a, Int)]) |- x.snd.hd.fst : a = 
            let test = [("x", Local, forall ["a"] (typ @(TVar "a", [(TVar "a", Int)])))] |=
                        (fd "x" [Snd def, Hd def, Fst def], typ @(TVar "sigma")) ~= (typ @(TVar "a"), [])
            executeCoreTests [test] typeCheckExpr'


test_type_check_expr_1 = do
            -- 5 :: σ = σ |-> Int
            let test = [] |= (iexpr 5, typ @(TVar "sigma")) ~= (typ @Int, [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_2 = do
            -- True :: σ = σ |-> Bool
            let test = [] |= (expr True, typ @Bool) ~= (typ @Bool, [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_3 = do
            -- 'c' :: σ = σ |-> Char
            let test = [] |= (expr 'c', typ @(TVar "sigma")) ~= (typ @Char, [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_4 = do
            -- [] :: σ = σ |-> [?a]i
            let test = [] |= (emptyList, typ @(TVar "sigma")) ~= (typ @[TVar "a"], [])
            executeCoreTests [test] typeCheckExpr'
            
test_type_check_expr_5 = do
            -- ('c', []) :: σ = σ |-> (Char, [?'l2]), ...
            let test = [] |= (expr ('c', emptyList) , typ @(TVar "sigma")) ~= (typ @(Char, [TVar "a"]), [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_6 = do
            -- -(5 + 8) :: Int
            let test = [] |= (op1 UnMinus (op2 (iexpr 5) Plus (iexpr 2)), typ @(TVar "sigma"))
                             ~= (typ @Int, [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_7 = do
            -- 'c' : [] :: [Char]
            let test = [] |= (op2 'c' Cons emptyList, typ @(TVar "sigma"))
                             ~= (typ @[Char], [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_8 = do
            -- x.hd :: v? 
            let test = [("x", Local, forall [] $ typ @[TVar "v?"])] |=
                        (expr (fd "x" [Hd def]), typ @(TVar "sigma"))
                        ~= (typ @(TVar "v?"), [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_9 = do
            -- x :: [Int] |- x.hd : x :: [Int] = 
            let test = [("x", Local, forall [] (typ @[Int]))] |=
                        (op2 (fd "x" [Hd def]) Cons (fd "x" []), 
                        typ @(TVar "sigma"))
                        ~= (typ @[Int], [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_10 = do
            -- x :: [Int] |- x.hd : x :: [Int] = 
            let test = [("x", Local, forall ["a"] (typ @[Int]))] |=
                         (op2 (fd "x" [Hd def]) Cons (fd "x" []),
                         typ @(TVar "sigma"))
                        ~= (typ @[Int], [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_11 = do
            -- id :: a -> a |- (id 'c') : [] :: [Char] 
            let test = [("id", GlobalFun, forall ["a"] $ typ @('[TVar "a"] --> TVar "a"))] |=
                         (op2 (fun1 "id" 'c') Cons emptyList, 
                         typ @(TVar "sigma"))
                        ~= (typ @[Char], [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_12 = do
            -- const :: a -> b -> a |- const True :: b -> Bool
            let test = [("const", GlobalFun, forall ["a", "b"] $ typ @('[TVar "a", TVar "b"] --> TVar "a"))] |=
                        (expr $ fun2 "const" True emptyList, typ @(TVar "sigma"))
                        ~= (typ @(Bool), [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_13 = do
            -- repl :: Int -> Char -> [Char]  |- hd (repl 3 'c') :: Char
            let test = [("repl", GlobalFun, forall [] $ typ @('[Int, Char] --> [Char]))] |=
                        (expr $ fun1 "hd" (fun2 "repl" (iexpr 3) 'c'),
                         typ @(TVar "sigma"))
                        ~= (typ @Char, [])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_14 = do
            -- 'c' >= 'd' :: Bool 
            let test = [] |= (op2 'c' GreaterEq 'd', typ @(TVar "sigma")) ~= (typ @(Bool), [TOrd $ typ @Char])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_15 = do
            -- x :: a |- x >= x :: Bool
            let test = [("x", Local, forall [] $ typ @(TVar "a"))] |= 
                    (op2 (fd "x" []) GreaterEq (fd "x" []), typ @(TVar "sigma")) ~= (typ @(Bool), [TOrd $ typ @(TVar "a")])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_16 = do
            -- x :: a |- (-x) >= x :: Bool
            let test = [("x", Local, forall [] $ typ @(TVar "a"))] |= 
                    (op2 (op1 UnMinus (fd "x" [])) GreaterEq (fd "x" []), typ @(TVar "sigma")) ~= (typ @Bool, [TOrd $ typ @Int])
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_17 = do
            -- const :: a -> b -> a |- hd (const True []) = fail
            let test = [("const", GlobalFun, forall ["a","b"] $ typ @('[TVar "a", TVar "b"] --> TVar "a"))] |=
                        expr (fun1 "hd" $ fun2 "const" True emptyList) ~\= typ @(TVar "sigma")
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_18 = do
            -- x :: a |- (-x) >= (x . tl) :: ?v = fail
            let test = [("x", Local, forall [] $ typ @(TVar "a"))] |= 
                        (op2 (op1 UnMinus (fd "x" [])) GreaterEq (fd "x" [Tl def])) ~\= typ @Bool
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_19 = do
            -- True >= t :: ?v = Fail
            let test = [] |= op2 True GreaterEq (iexpr 5) ~\= typ @(TVar "sigma")
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_20 = do
            -- True <= False :: ?v = Fail
            let test = [] |= (op2 True LessEq False, typ @(TVar "sigma")) ~= (typ @Bool, [TOrd $ typ @Bool])
            executeCoreTests [test] typeCheckExpr'


test_type_check_expr_21 = do
            -- !('c' : []) :: ?v = Fail
            let test = [] |= op1 UnNeg (op2 'c' Cons emptyList) ~\= typ @(TVar "sigma")
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_22 = do
            -- !('c' : []) :: ?v = Fail
            let test = [] |= op1 UnNeg (op2 'c' Cons emptyList) ~\= typ @(TVar "sigma")
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_23 = do
            -- 'c' : 'd' :: ?v = Fail
            let test = [] |= op2 'c' Cons 'd' ~\= typ @(TVar "sigma")
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_24 = do
            -- [] :: Int = Fail
            let test = [] |= emptyList ~\= typ @Int
            executeCoreTests [test] typeCheckExpr'

test_type_check_expr_25 = do
            -- 'c' + 'd' :: ?v = Fail
            let test = [] |= op2 'c' Plus 'd' ~\= typ @(TVar "sigma")
            executeCoreTests [test] typeCheckExpr'


typeCheckVarDecl' a _ = (\v@(CoreVarDecl _ t _ _) -> (v, t)) <$> typeCheckVarDecl a

test_type_check_var_decl_1 = do
                -- Int x = 5
                let test = [] |= ("x", typ @Int, []) =:: iexpr 5
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_2 = do
                -- Char x = 'c'
                let test = [] |= ("x", typ @Char, []) =:: expr 'c'
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_3 = do
                -- Bool x = False 
                let test = [] |= ("x", typ @Bool, []) =:: expr False
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_4 = do
                -- y :: Bool |= Bool x = y
                let test = [("y", Local, forall [] $ typ @Bool)] |= ("x", typ @Bool, []) =:: expr (fd "y" [])
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_5 = do
                -- [a] x = []
                let test = [] |= ("x", typ @[TVar "a"], []) =:: emptyList
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_6 = do
                -- [a] x = (Bool, [])
                let test = [] |= ("x", typ @(Bool, [TVar "a"]), []) =:: expr (False, emptyList)
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_7 = do
                -- [Int] x = (Bool, [])
                let test = [] |= ("x", typ @(Bool, [TVar "a"]), []) =:: expr (False, emptyList)
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_8 = do
                -- [Int] x = 5 >= 3
                let test = [] |= ("x", typ @Bool, [TOrd $ typ @Int]) =:: op2 (iexpr 5) GreaterEq (iexpr 3)
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_9 = do
                -- x :: a |- Var y = x == x
                let test = [("x", Local, forall [] $ typ @(TVar "a"))] |= 
                            ("y", typ @Bool, [TEq $ typ @(TVar "a")]) =:: op2 (fd "x" []) Equal (fd "x" [])
                executeCoreTests [test] typeCheckVarDecl'

test_type_check_var_decl_10 = do
                -- id : forall a. a -> a |- (b -> b) x = id
                let test = [("id", GlobalFun, forall ["a"] $ typ @('[TVar "a"] --> TVar "a"))] |= 
                            ("x", typ @('[TVar "a"] --> TVar "a"), []) =:: expr (fd "id" [])
                executeCoreTests [test] typeCheckVarDecl'
                
test_type_check_var_decl_11 = do
                -- id : forall a. a -> a |- (a -> b) x = id :: fail
                let test = [("id", GlobalFun, forall ["a"] $ typ @('[TVar "a"] --> TVar "a"))] |= 
                            ("x", typ @('[TVar "a"] --> TVar "b")) =\: expr (fd "id" [Hd def])
                executeCoreTests [test] typeCheckVarDecl'

typeCheckStmt' a t = (\s -> (s, t)) <$> typeCheckStmt a t

test_type_check_stmt_1 = do
                -- if True { return False } else { return True } :: Bool
                let test = [] |= (ite True [ret False] [ret True], typ @(TVar "a")) ~= (typ @Bool, [])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_2 = do
                -- if True {} :: ?a
                let test = [] |= (ite True [] [], typ @(TVar "a")) ~= (typ @(TVar "a"), [])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_3 = do
                -- x :: a |- if True { print(x == x); } :: ?a
                let test = [("x", Local, forall [] $ typ @(TVar "a"))] |= 
                        (ite True [stmt $ fun1 "print" (op2 (fd "x" []) Nequal (fd "x" []))] [], typ @(TVar "a")) 
                        ~= (typ @(TVar "a"), [TPrint $ typ @Bool, TEq $ typ @(TVar "a")])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_4 = do
                -- x :: a, id :: forall a. a -> a |- if True { print(x == x); } else { id(x >= 5) } :: ?a, [Print Bool, Eq Int, Ord Int]
                let test = [("x", Local, forall [] $ typ @(TVar "a")), ("id", GlobalFun, forall ["b"] $ typ @('[TVar "b"] --> TVar "b"))] |= 
                            (ite True [stmt $ fun1 "print" (op2 (fd "x" []) Nequal (fd "x" []))] 
                                  [stmt $ fun1 "id" (op2 (fd "x" []) GreaterEq (iexpr 5))], typ @(TVar "b")) 
                            ~= (typ @(TVar "b"), [TPrint $ typ @Bool, TEq $ typ @Int, TOrd $ typ @Int])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_5 = do
                -- if True { return [False] } else { return [True] } :: [Bool]
                let test = [] |= (ite True [ret [False]] [ret [True]], typ @[TVar "a"]) ~= (typ @[Bool], [])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_6 = do
                -- if True { return [] } else { return [] } :: [Int]
                let test = [] |= (ite True [ret emptyList] [ret emptyList], typ @[Int]) ~= (typ @[Int], [])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_7 = do
                -- while (True) { return [] } :: [?a]
                let test = [] |= (while True [ret emptyList], typ @(TVar "a")) ~= (typ @[TVar "b"], [])
                executeCoreTests [test] typeCheckStmt'
                
test_type_check_stmt_8 = do
                -- while (True) { print (5); return [] } :: [?a], Printable Int
                let test = [] |= (while True [stmt $ fun1 "print" (iexpr 5), ret emptyList], typ @(TVar "a")) 
                            ~= (typ @[TVar "b"], [TPrint $ typ @Int])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_9 = do
                -- x : a |- while (True) { x = 5; return x; } :: Int
                let test = [("x", Local, forall [] $ typ @(TVar "a"))] |= 
                        (while True [ ("x",[]) =: iexpr 5, ret (fd "x" [])], typ @(TVar "b")) ~= (typ @Int, [])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_10 = do
                -- id : forall a. a -> a |- while (True) { id(5); return id; } :: b -> b
                let test = [("id", GlobalFun, forall ["a"] $ typ @('[TVar "a"] --> TVar "a"))] |= 
                        (while True [ stmt (fun1 "id" (iexpr 5)), ret (fd "id" []) ], typ @(TVar "b")) 
                                ~= (typ @('[TVar "c"] --> TVar "c"), [])
                executeCoreTests [test] typeCheckStmt'
                
test_type_check_stmt_11 = do
                -- x : [a] |- while (True) { x = []; x.hd = 3; return x; } :: [Int]
                let test = [("x", Local, forall [] $ typ @[TVar "a"])] |= 
                        (while True [ ("x",[]) =: emptyList, 
                                      ("x",[Hd def]) =: iexpr 3, 
                                      ret (fd "x" []) ], typ @(TVar "b")) ~= (typ @[Int], [])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_12 = do
                -- x : [[(a,b)]] |- while (True) { x.tl.hd.fst = 3; return x; } :: [[(Int, b)]]
                let test = [("x", Local, forall [] $ typ @[[(TVar "a", TVar "b")]])] |= 
                        (while True [ ("x",[Tl def, Hd def, Hd def, Fst def]) =: iexpr 3, 
                                      ret (fd "x" []) ], typ @(TVar "c")) ~= (typ @[[(Int, TVar "b")]], [])
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_13 = do
                -- while (True) { return True; return; } fail
                let test = [] |= while True [ ret True, retVoid ] ~\= typ @(TVar "b")
                executeCoreTests [test] typeCheckStmt'
                
test_type_check_stmt_14 = do
                -- while ('c') { return True; } :: fail
                let test = [] |= while 'c' [ ret True ] ~\= typ @(TVar "a")
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_15 = do
                -- if (5) { return False } { return True } fail
                let test = [] |= ite (iexpr 5) [ret False] [ret True] ~\= typ @(TVar "a")
                executeCoreTests [test] typeCheckStmt'

test_type_check_stmt_16 = do
                -- if (True) { return False } { return 5 } fail
                let test = [] |= ite (True) [ret False] [ret (iexpr 5)] ~\= typ @(TVar "a")
                executeCoreTests [test] typeCheckStmt'


typeCheckFunDecl' v _ = typeCheckFunDecls (CyclicSCC [v]) >>= 
                        \([x@(CoreFunDecl _ _ _ t _)]) -> (getTCons .= S.fromList (getTCon t)) $> (x, updateTCon [] t) 

test_type_check_fun_decl_1 = do
                -- id (x) :: b -> b { return x; } :: a -> a
                let test = [] |= declare "id" ["x"] [] [ ret (fd "x" []) ] 
                                 .:: (typ @('[TVar "a"] --> TVar "a"), [])
                executeCoreTests [test] typeCheckFunDecl' 

test_type_check_fun_decl_2 = do
                -- foo (x) :: Int -> Bool { var z = x != 5; return z; } :: Bool -> Int, TEq Int
                let test = [] |= declare "foo" ["x"]
                                    [ defineI "z" (op2 (fd "x" []) Nequal (iexpr 5)) ] 
                                    [ ret (fd "z" []) ] .:: (typ @('[Int] --> Bool), [])
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_3 = do
                -- foo (x) :: Int -> Int { var y = x + 5; return y; } :: Int -> Int
                let test = [] |= declare "foo" ["x"] 
                                    [ defineI "y" (op2 (fd "x" []) Plus (iexpr 5)) ] 
                                    [ ret (fd "y" []) ] .:: (typ @('[Int] --> Int), [])
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_4 = do
                -- fact (x) :: Int -> Int { Var r = x * fact(x - 1); return r; } :: Int -> Int
                let test = [] |= declare "fact" ["x"]
                                    [ defineI "r" (op2 (fd "x" []) Mul (fun1 "fact" (op2 (fd "x" []) Minus (iexpr 1)))) ] 
                                    [ ret (fd "r" []) ] .:: (typ @('[Int] --> Int), [])
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_5 = do
                -- infId (x) :: a -> a { Var z = weirdId(x); return x; } :: a -> a
                let test = [] |= declare "weirdId" ["x"]
                                            [defineI "z" (expr $ fun1 "weirdId" (fd "x" []))]
                                            [ ret (fd "x" []) ] 
                                            .:: (typ @('[TVar "a"] --> TVar "a"), [])
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_6 = do
                -- idPrint (x) :: a -> a { print(x); return x; }; :: a -> a, Print a
                let test = [] |= declare "idPrint" ["x"]
                                            []
                                            [ stmt $ fun1 "print" (fd "x" []), ret (fd "x" []) ] 
                                            .:: (typ @('[TVar "a"] --> TVar "a"), [TPrint $ typ @(TVar "a")])
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_7 = do
                -- constPrint (x, y) :: a -> b -> a { print(y); return x; } } :: a -> b -> a
                let test = [] |= declare "constPrint" ["x", "y"]
                                            []
                                            [ stmt (fun1 "print" (fd "y" [])),  ret (fd "x" []) ] 
                                            .:: (typ @('[TVar "a", TVar "b"] --> TVar "a"), [])
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_8 = do
                -- constPrint (x, y) :: a -> b -> a { print(y); return x; } } :: a -> b -> a
                let test = [] |= declare "constPrint" ["x", "y"]
                                            []
                                            [ stmt (fun1 "print" (fd "y" [])),  ret (fd "x" []) ] 
                                            .:: (typ @('[TVar "a", TVar "b"] --> TVar "a"), [])
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_9 = do
                -- constPrint (x, y) { return x; } } :: a -> b -> a
                let test = [] |= declare "constPrint" ["x", "y"]
                                            []
                                            [ ret (fd "x" []) ] 
                                            .:: (typ @('[TVar "a", TVar "b"] --> TVar "a"), [])
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_10 = do
                -- intId (x) { Var z = invalidId(5); return x; } :: Int -> Int
                let test = [] |= declare "invalidId" ["x"]
                                          [defineI "z" (expr $ fun1 "invalidId" (iexpr 5))]
                                          [ ret (fd "x" []) ]
                                          .:: (typ @('[Int] --> Int), []) 
                executeCoreTests [test] typeCheckFunDecl'

test_type_check_fun_decl_11 = do
                -- infinite(x) { return f( (x, x) ); }
                let test = [] |= failure (declare "infinite" ["x"] []
                                          [ret (fun1 "infinite" [(fd "x" [], fd "x" [])])])
                                          (typ @('[TVar "a"] --> TVar "b"))
                executeCoreTests [test] typeCheckFunDecl'
