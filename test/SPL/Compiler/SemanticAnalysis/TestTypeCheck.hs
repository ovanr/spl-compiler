{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Redundant bracket" #-}

module SPL.Compiler.SemanticAnalysis.TestTypeCheck (htf_thisModulesTests) where

import Test.Framework
import Control.Monad
import Data.Default
import Data.Tuple
import Data.Bifunctor
import Data.Text (Text)
import Data.Set (Set)
import Control.Monad.State
import qualified Data.Set as S
import qualified Data.Map as M

import SPL.Compiler.Common.Testable
import SPL.Compiler.SemanticAnalysis.Testable
import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TypeCheck.TCon
import SPL.Compiler.SemanticAnalysis.TypeCheck.Env (initGamma)
import SPL.Compiler.SemanticAnalysis.TypeCheck
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import SPL.Compiler.SemanticAnalysis.TypeProperty

type TypeCheckTest a = ((a, TCTType), Maybe (TCTType, [TCon])) 
type TypeCheckTestEnv a = ((TypeEnv, a, TCTType), Maybe (TCTType, [TCon]))

forall :: [Text] -> TCTType -> Scheme
forall vars = Scheme (S.fromList vars)

-- Shorthand operators to create a type check tests

infixl 2 ~=
(~=) :: (a, TCTType) -> (TCTType, [TCon]) -> TypeCheckTest a
(a, t) ~= (typ, tcon) = ((a, t), Just (typ,tcon))

infixl 2 ~\=
(~\=) :: a -> TCTType -> TypeCheckTest a
a ~\= t = ((a, t), Nothing)

infixl 2 .::
(.::) :: TCTFunDecl -> (TCTType, [TCon]) -> TypeCheckTest TCTFunDecl
f@(TCTFunDecl _ _ _ tau _) .:: (typ,tcon) = ((f, tau), Just (typ, tcon))

failure :: TCTFunDecl -> TypeCheckTest TCTFunDecl
failure f@(TCTFunDecl _ _ _ tau _) = ((f, tau), Nothing)

infixl 2 =:: 
(=::) :: (Text, TCTType, [TCon]) -> TCTExpr -> TypeCheckTest TCTVarDecl
(=::) (id, t, tcon) e = 
    ((TCTVarDecl def t (TCTIdentifier def id) e, t), Just (t,tcon))

infixl 2 =\:
(=\:) :: (Text, TCTType) -> TCTExpr -> TypeCheckTest TCTVarDecl
(=\:) (id, t) e  = 
    ((TCTVarDecl def t (TCTIdentifier def id) e, t), Nothing)

infixl 1 |= 
(|=) :: [(Text, Scheme)] -> TypeCheckTest a -> TypeCheckTestEnv a
(|=) env ((a, t), r) = ((TypeEnv . M.fromList . map (second (Global,)) $ env, a, t), r)

thd3 :: (a,b,c) -> c
thd3 (_,_,x) = x

snd3 :: (a,b,c) -> b
snd3 (_,x,_) = x

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

executeTCTests :: Show a => [TypeCheckTestEnv a] ->
                  (TypeEnv -> a -> TCTType -> TCMonad (Set TCon, a, Subst, TCTType)) ->
                  IO ()
executeTCTests tests evaluator =
    forM_ tests $ \((gamma, a, initialTyp), expected) -> do
        let state = TypeCheckState 0 mempty mempty
        let actual = fst <$> runStateT (evaluator (initGamma <> gamma) a initialTyp) state
        case expected of
            Just (expectedTyp, expectedTCon) ->
                case actual of
                    Right (actualTCon, _, actualSubst, actualTyp) -> do 
                        -- compare up types up to alpha eq
                        assertEqual expectedTyp (toTestForm (actualSubst $* actualTyp))

                        -- compare type constraints via strict eq
                        let renameSubst = matchVars expectedTyp (actualSubst $* actualTyp)
                        mapM_ (\con -> assertElem con $ S.toList (actualSubst $* actualTCon)) 
                              (renameSubst <> actualSubst $* expectedTCon)

                    Left err -> assertFailure $ "expected substitution but got failure: " <> show err

            Nothing -> print actual >> void (assertLeft actual)

matchVars :: TCTType -> TCTType -> Subst
matchVars (TCTVarType _ a) v = Subst $ M.singleton a v
matchVars (TCTListType _ t1) (TCTListType _ t2) = matchVars t1 t2
matchVars (TCTTupleType _ a1 b1) (TCTTupleType _ a2 b2) = matchVars b1 b2 <> matchVars a1 a2 
matchVars (TCTFunType _ _ a1 b1) (TCTFunType _ _ a2 b2) = matchVars b1 b2 <> matchVars a1 a2 
matchVars _ _ = mempty

typeCheckExpr' e a t = (\(a, b, c) -> (a, b, c, t)) <$> typeCheckExpr e a t

test_type_check_expr_1 = do
            -- 5 :: σ = σ |-> Int
            let test = [] |= (iexpr 5, typ @(Var "sigma")) ~= (typ @Int, [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_2 = do
            -- True :: σ = σ |-> Bool
            let test = [] |= (expr True, typ @Bool) ~= (typ @Bool, [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_3 = do
            -- 'c' :: σ = σ |-> Char
            let test = [] |= (expr 'c', typ @(Var "sigma")) ~= (typ @Char, [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_4 = do
            -- [] :: σ = σ |-> [?a]i
            let test = [] |= (emptyList, typ @(Var "sigma")) ~= (typ @[Var "a"], [])
            executeTCTests [test] typeCheckExpr'
            
test_type_check_expr_5 = do
            -- ('c', []) :: σ = σ |-> (Char, [?'l2]), ...
            let test = [] |= (expr ('c', emptyList) , typ @(Var "sigma")) ~= (typ @(Char, [Var "a"]), [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_6 = do
            -- -(5 + 8) :: Int
            let test = [] |= (op1 UnMinus (op2 (iexpr 5) Plus (iexpr 2)), typ @(Var "sigma"))
                             ~= (typ @Int, [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_7 = do
            -- 'c' : [] :: [Char]
            let test = [] |= (op2 'c' Cons emptyList, typ @(Var "sigma"))
                             ~= (typ @[Char], [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_8 = do
            -- x.hd :: v? 
            let test = [("x", forall [] $ typ @[Var "v?"])] |=
                        (expr (fd "x" [Hd def]), typ @(Var "sigma"))
                        ~= (typ @(Var "v?"), [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_9 = do
            -- x :: [Int] |- x.hd : x :: [Int] = 
            let test = [("x", forall [] (typ @[Int]))] |=
                        (op2 (fd "x" [Hd def]) Cons (fd "x" []), 
                        typ @(Var "sigma"))
                        ~= (typ @[Int], [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_10 = do
            -- x :: [Int] |- x.hd : x :: [Int] = 
            let test = [("x", forall ["a"] (typ @[Int]))] |=
                         (op2 (fd "x" [Hd def]) Cons (fd "x" []),
                         typ @(Var "sigma"))
                        ~= (typ @[Int], [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_11 = do
            -- id :: a -> a |- (id 'c') : [] :: [Char] 
            let test = [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |=
                         (op2 (fun1 "id" 'c') Cons emptyList, 
                         typ @(Var "sigma"))
                        ~= (typ @[Char], [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_12 = do
            -- const :: a -> b -> a |- const True :: b -> Bool
            let test = [("const", forall ["a", "b"] $ typ @(Var "a" -> Var "b" -> Var "a"))] |=
                        (expr $ fun1 "const" True, typ @(Var "sigma"))
                        ~= (typ @(Var "b" -> Bool), [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_13 = do
            -- repl :: Int -> Char -> [Char]  |- hd (repl 3 'c') :: Char
            let test = [("repl", forall [] $ typ @(Int -> Char -> [Char]))] |=
                        (expr $ fun1 "hd" (fun2 "repl" (iexpr 3) 'c'),
                         typ @(Var "sigma"))
                        ~= (typ @Char, [])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_14 = do
            -- 'c' >= 'd' :: Bool 
            let test = [] |= (op2 'c' GreaterEq 'd', typ @(Var "sigma")) ~= (typ @(Bool), [TOrd $ typ @Char])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_15 = do
            -- x :: a |- x >= x :: Bool
            let test = [("x", forall [] $ typ @(Var "a"))] |= 
                    (op2 (fd "x" []) GreaterEq (fd "x" []), typ @(Var "sigma")) ~= (typ @(Bool), [TOrd $ typ @(Var "a")])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_16 = do
            -- x :: a |- (-x) >= x :: Bool
            let test = [("x", forall [] $ typ @(Var "a"))] |= 
                    (op2 (op1 UnMinus (fd "x" [])) GreaterEq (fd "x" []), typ @(Var "sigma")) ~= (typ @Bool, [TOrd $ typ @Int])
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_17 = do
            -- const :: a -> b -> a |- hd (const True []) = fail
            let test = [("const", forall ["a","b"] $ typ @(Var "a" -> Var "b" -> Var "a"))] |=
                        expr (fun1 "hd" $ fun2 "const" True emptyList) ~\= typ @(Var "sigma")
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_18 = do
            -- x :: a |- (-x) >= (x . tl) :: ?v = fail
            let test = [("x", forall [] $ typ @(Var "a"))] |= 
                        (op2 (op1 UnMinus (fd "x" [])) GreaterEq (fd "x" [Tl def])) ~\= typ @Bool
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_19 = do
            -- True >= t :: ?v = Fail
            let test = [] |= op2 True GreaterEq (iexpr 5) ~\= typ @(Var "sigma")
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_20 = do
            -- True <= False :: ?v = Fail
            let test = [] |= op2 True LessEq False ~\= typ @(Var "sigma")
            executeTCTests [test] typeCheckExpr'


test_type_check_expr_21 = do
            -- !('c' : []) :: ?v = Fail
            let test = [] |= op1 UnNeg (op2 'c' Cons emptyList) ~\= typ @(Var "sigma")
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_22 = do
            -- !('c' : []) :: ?v = Fail
            let test = [] |= op1 UnNeg (op2 'c' Cons emptyList) ~\= typ @(Var "sigma")
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_23 = do
            -- 'c' : 'd' :: ?v = Fail
            let test = [] |= op2 'c' Cons 'd' ~\= typ @(Var "sigma")
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_24 = do
            -- [] :: Int = Fail
            let test = [] |= emptyList ~\= typ @Int
            executeTCTests [test] typeCheckExpr'

test_type_check_expr_25 = do
            -- 'c' + 'd' :: ?v = Fail
            let test = [] |= op2 'c' Plus 'd' ~\= typ @(Var "sigma")
            executeTCTests [test] typeCheckExpr'


typeCheckVarDecl' e a _ = (\(a, v@(TCTVarDecl _ t _ _), c) -> (a, v, c, t)) <$> typeCheckVarDecl e a

test_type_check_var_decl_1 = do
                -- Int x = 5
                let test = [] |= ("x", typ @Int, []) =:: iexpr 5
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_2 = do
                -- Char x = 'c'
                let test = [] |= ("x", typ @Char, []) =:: expr 'c'
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_3 = do
                -- Bool x = False 
                let test = [] |= ("x", typ @Bool, []) =:: expr False
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_4 = do
                -- y :: Bool |= Bool x = y
                let test = [("y", forall [] $ typ @Bool)] |= ("x", typ @Bool, []) =:: expr (fd "y" [])
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_5 = do
                -- [a] x = []
                let test = [] |= ("x", typ @[Var "a"], []) =:: emptyList
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_6 = do
                -- [a] x = (Bool, [])
                let test = [] |= ("x", typ @(Bool, [Var "a"]), []) =:: expr (False, emptyList)
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_7 = do
                -- [Int] x = (Bool, [])
                let test = [] |= ("x", typ @(Bool, [Int]), []) =:: expr (False, emptyList)
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_8 = do
                -- [Int] x = 5 >= 3
                let test = [] |= ("x", typ @Bool, [TOrd $ typ @Int]) =:: op2 (iexpr 5) GreaterEq (iexpr 3)
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_9 = do
                -- x :: a |- Var y = x == x
                let test = [("x", forall [] $ typ @(Var "a"))] |= 
                            ("y", typ @Bool, [TEq $ typ @(Var "a")]) =:: op2 (fd "x" []) Equal (fd "x" [])
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_10 = do
                -- id : forall a. a -> a |- (b -> b) x = id
                let test = [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |= 
                            ("x", typ @(Var "a" -> Var "a"), []) =:: expr (fd "id" [])
                executeTCTests [test] typeCheckVarDecl'
                
test_type_check_var_decl_11 = do
                -- id : forall a. a -> a |- (a -> b) x = id :: fail
                let test = [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |= 
                            ("x", typ @(Var "a" -> Var "b")) =\: expr (fd "id" [])
                executeTCTests [test] typeCheckVarDecl'

test_type_check_var_decl_12 = do
                -- a x = 5 :: fail
                let test = [] |= ("x", typ @(Var "a")) =\: iexpr 5 
                executeTCTests [test] typeCheckVarDecl'

typeCheckStmt' e a t = (\(a, s, c) -> (a, s, c, t)) <$> typeCheckStmt e a t

test_type_check_stmt_1 = do
                -- if True { return False } else { return True } :: Bool
                let test = [] |= (ite True [ret False] [ret True], typ @(Var "a")) ~= (typ @Bool, [])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_2 = do
                -- if True {} :: ?a
                let test = [] |= (ite True [] [], typ @(Var "a")) ~= (typ @(Var "a"), [])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_3 = do
                -- if True { print(x == x); } :: ?a
                let test = [("x", forall [] $ typ @(Var "a"))] |= 
                        (ite True [stmt $ fun1 "print" (op2 (fd "x" []) Nequal (fd "x" []))] [], typ @(Var "a")) 
                        ~= (typ @(Var "a"), [TPrint $ typ @Bool, TEq $ typ @(Var "a")])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_4 = do
                -- id :: forall a. a -> a |- if True { print(x == x); } else { id(x >= 5) } :: ?a, [Print Bool, Eq Int, Ord Int]
                let test = [("x", forall [] $ typ @(Var "a")), ("id", forall ["b"] $ typ @(Var "b" -> Var "b"))] |= 
                            (ite True [stmt $ fun1 "print" (op2 (fd "x" []) Nequal (fd "x" []))] 
                                  [stmt $ fun1 "id" (op2 (fd "x" []) GreaterEq (iexpr 5))], typ @(Var "b")) 
                            ~= (typ @(Var "b"), [TPrint $ typ @Bool, TEq $ typ @Int, TOrd $ typ @Int])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_5 = do
                -- if True { return [False] } else { return [True] } :: [Bool]
                let test = [] |= (ite True [ret [False]] [ret [True]], typ @[Var "a"]) ~= (typ @[Bool], [])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_6 = do
                -- if True { return [] } else { return [] } :: [Int]
                let test = [] |= (ite True [ret emptyList] [ret emptyList], typ @[Int]) ~= (typ @[Int], [])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_7 = do
                -- while (True) { return [] } :: [?a]
                let test = [] |= (while True [ret emptyList], typ @(Var "a")) ~= (typ @[Var "b"], [])
                executeTCTests [test] typeCheckStmt'
                
test_type_check_stmt_8 = do
                -- while (True) { print (5); return [] } :: [?a], Printable Int
                let test = [] |= (while True [stmt $ fun1 "print" (iexpr 5), ret emptyList], typ @(Var "a")) 
                            ~= (typ @[Var "b"], [TPrint $ typ @Int])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_9 = do
                -- x : a |- while (True) { x = 5; return x; } :: Int
                let test = [("x", forall [] $ typ @(Var "a"))] |= 
                        (while True [ fd "x" [] =: iexpr 5, ret (fd "x" [])], typ @(Var "b")) ~= (typ @Int, [])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_10 = do
                -- id : forall a. a -> a |- while (True) { id(5); return id; } :: b -> b
                let test = [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |= 
                        (while True [ stmt (fun1 "id" (iexpr 5)), ret (fd "id" []) ], typ @(Var "b")) 
                                ~= (typ @(Var "c" -> Var "c"), [])
                executeTCTests [test] typeCheckStmt'
                
test_type_check_stmt_11 = do
                -- x : [a] |- while (True) { x = []; x.hd = 3; return x; } :: [Int]
                let test = [("x", forall [] $ typ @[Var "a"])] |= 
                        (while True [ fd "x" [] =: emptyList, 
                                      fd "x" [Hd def] =: iexpr 3, 
                                      ret (fd "x" []) ], typ @(Var "b")) ~= (typ @[Int], [])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_12 = do
                -- x : [[(a,b)]] |- while (True) { x.tl.hd.fst = 3; return x; } :: [[(Int, b)]]
                let test = [("x", forall [] $ typ @[[(Var "a", Var "b")]])] |= 
                        (while True [ fd "x" [Tl def, Hd def, Hd def, Fst def] =: iexpr 3, 
                                      ret (fd "x" []) ], typ @(Var "c")) ~= (typ @[[(Int, Var "b")]], [])
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_13 = do
                -- while (True) { return True; return; } fail
                let test = [] |= while True [ ret True, retVoid ] ~\= typ @(Var "b")
                executeTCTests [test] typeCheckStmt'
                
test_type_check_stmt_14 = do
                -- while ('c') { return True; } :: fail
                let test = [] |= while 'c' [ ret True ] ~\= typ @(Var "a")
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_15 = do
                -- if (5) { return False } { return True } fail
                let test = [] |= ite (iexpr 5) [ret False] [ret True] ~\= typ @(Var "a")
                executeTCTests [test] typeCheckStmt'

test_type_check_stmt_16 = do
                -- if (True) { return False } { return 5 } fail
                let test = [] |= ite (True) [ret False] [ret (iexpr 5)] ~\= typ @(Var "a")
                executeTCTests [test] typeCheckStmt'



typeCheckFunDecl' e v _ = (\(x@(TCTFunDecl _ _ _ t _),y) -> (getTypeCon t, x, y, t)) <$> typeCheckFunDecl e v

test_type_check_fun_decl_1 = do
                -- id (x) :: b -> b { return x; } :: a -> a
                let test = [] |= declare "id" ["x"] (typ @(Var "b" -> Var "b")) 
                                    [ ] [ ret (fd "x" []) ] .:: (typ @(Var "a" -> Var "a"), [])
                executeTCTests [test] typeCheckFunDecl' 

test_type_check_fun_decl_2 = do
                -- foo (x) :: Int -> Bool { var z = x != 5; return z; } :: Bool -> Int, TEq Int
                let test = [] |= declare "foo" ["x"] (typ @(Int -> Bool)) 
                                    [ defineI "z" (op2 (fd "x" []) Nequal (iexpr 5)) ] 
                                    [ ret (fd "z" []) ] .:: (typ @(Int -> Bool), [TEq $ typ @Int])
                executeTCTests [test] typeCheckFunDecl'
test_type_check_fun_decl_3 = do
                -- foo (x) :: Int -> Int { var y = x + 5; return y; } :: Int -> Int
                let test = [] |= declare "foo" ["x"] (typ @(Int -> Int)) 
                                    [ defineI "y" (op2 (fd "x" []) Plus (iexpr 5)) ] 
                                    [ ret (fd "y" []) ] .:: (typ @(Int -> Int), [])
                executeTCTests [test] typeCheckFunDecl'

test_type_check_fun_decl_4 = do
                -- fact (x) :: Int -> Int { Var r = x * fact(x - 1); return r; } :: Int -> Int
                let test = [] |= declare "fact" ["x"] (typ @(Int -> Int)) 
                                    [ defineI "r" (op2 (fd "x" []) Mul (fun1 "fact" (op2 (fd "x" []) Minus (iexpr 1)))) ] 
                                    [ ret (fd "r" []) ] .:: (typ @(Int -> Int), [])
                executeTCTests [test] typeCheckFunDecl'

test_type_check_fun_decl_5 = do
                -- infId (x) :: a -> a { Var z = weirdId(x); return x; } :: a -> a
                let test = [] |= declare "weirdId" ["x"] (typ @(Var "a" -> Var "a")) 
                                            [defineI "z" (expr $ fun1 "weirdId" (fd "x" []))]
                                            [ ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "a"), [])
                executeTCTests [test] typeCheckFunDecl'

test_type_check_fun_decl_6 = do
                -- idPrint (x) :: a -> a { print(x); return x; }; :: a -> a, Print a
                let test = [] |= declare "idPrint" ["x"] (typ @(Var "a" -> Var "a")) 
                                            []
                                            [ stmt $ fun1 "print" (fd "x" []), ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "a"), [TPrint $ typ @(Var "a")])
                executeTCTests [test] typeCheckFunDecl'

test_type_check_fun_decl_7 = do
                -- constPrint (x, y) :: a -> b -> a { print(y); return x; } } :: a -> b -> a
                let test = [] |= declare "constPrint" ["x", "y"] (typ @(Var "a" -> Var "b" -> Var "a")) 
                                            []
                                            [ stmt (fun1 "print" (fd "y" [])),  ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "b" -> Var "a"), [])
                executeTCTests [test] typeCheckFunDecl'

test_type_check_fun_decl_8 = do
                -- constPrint (x, y) :: a -> b -> a { print(y); return x; } } :: a -> b -> a
                let test = [] |= declare "constPrint" ["x", "y"] (typ @(Var "a" -> Var "b" -> Var "a")) 
                                            []
                                            [ stmt (fun1 "print" (fd "y" [])),  ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "b" -> Var "a"), [])
                executeTCTests [test] typeCheckFunDecl'

test_type_check_fun_decl_9 = do
                -- constPrint (x, y) :: a -> a -> a { return x; } } :: a -> a -> a
                let test = [] |= declare "constPrint" ["x", "y"] (typ @(Var "a" -> Var "a" -> Var "a")) 
                                            []
                                            [ ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "a" -> Var "a"), [])
                executeTCTests [test] typeCheckFunDecl'

test_type_check_fun_decl_10 = do
                -- constPrint (x, y) :: a -> b -> b { return x; } } :: a -> b -> a
                let test = [] |= failure (declare "constPrint" ["x", "y"] (typ @(Var "a" -> Var "b" -> Var "b")) 
                                                    []
                                                    [ ret (fd "x" []) ] )
                executeTCTests [test] typeCheckFunDecl'

test_type_check_fun_decl_11 = do
                -- invalidId (x) :: a -> a { Var z = invalidId(5); return x; } :: a -> a
                let test = [] |= failure (declare "invalidId" ["x"] (typ @(Var "a" -> Var "a")) 
                                            [defineI "z" (expr $ fun1 "invalidId" (iexpr 5))]
                                            [ ret (fd "x" []) ])
                executeTCTests [test] typeCheckFunDecl'
