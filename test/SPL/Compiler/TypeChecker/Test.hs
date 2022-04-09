{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# HLINT ignore "Redundant bracket" #-}

module SPL.Compiler.TypeChecker.Test (htf_SPL_Compiler_TypeChecker_Test_thisModulesTests) where

import Test.Framework
import Control.Monad
import Data.Default
import Data.Tuple
import Data.Text (Text)
import Data.Set (Set)
import Control.Monad.State
import qualified Data.Set as S
import qualified Data.Map as M

import SPL.Compiler.Common.Testable
import SPL.Compiler.TypeChecker.Testable
import SPL.Compiler.TypeChecker.TCT
import SPL.Compiler.TypeChecker.TCon
import SPL.Compiler.TypeChecker.Env (initGamma)
import SPL.Compiler.TypeChecker.TypeCheck
import SPL.Compiler.TypeChecker.Unify
import SPL.Compiler.TypeChecker.TypeProperty

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
(|=) env ((a, t), r) = ((TypeEnv . M.fromList $ env, a, t), r)

thd3 :: (a,b,c) -> c
thd3 (_,_,x) = x

snd3 :: (a,b,c) -> b
snd3 (_,x,_) = x

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

executeTCTests :: Show a => [TypeCheckTestEnv a] ->
                  (TypeEnv -> a -> TCTType -> TCMonad (Set TCon, a, Subst)) ->
                  IO ()
executeTCTests tests evaluator =
    forM_ tests $ \((gamma, x, t), expected) -> do
        let st = TypeCheckState 0 mempty mempty
        let actual = fst <$> runStateT (evaluator (initGamma <> gamma) x t) st
        case expected of
            Just (typ, tcon) ->
                case actual of
                    Right (actTCon, _, actSubst) -> do 
                        assertEqual typ (toTestForm (actSubst $* t))
                        mapM_ (\con -> assertElem (actSubst $* con) $ S.toList (actSubst $* actTCon)) tcon
                    Left err -> assertFailure $ "expected substitution but got failure: " <> show err
            Nothing -> print actual >> void (assertLeft actual)

test_type_check_expr = do
    let tests = [
            -- 5 :: σ = σ |-> Int
            [] |= (iexpr 5, typ @(Var "sigma")) ~= (typ @Int, []),

            -- True :: σ = σ |-> Bool
            [] |= (expr True, typ @Bool) ~= (typ @Bool, []),

            -- 'c' :: σ = σ |-> Char
            [] |= (expr 'c', typ @(Var "sigma")) ~= (typ @Char, []),

            -- [] :: σ = σ |-> [?a]
            [] |= (emptyList, typ @(Var "sigma")) ~= (typ @[Var "a"], []),
            
            -- ('c', []) :: σ = σ |-> (Char, [?'l2]), ...
            [] |= (expr ('c', emptyList) , typ @(Var "sigma")) ~= (typ @(Char, [Var "a"]), []),

            -- -(5 + 8) :: Int
            [] |= (op1 UnMinus (op2 (iexpr 5) Plus (iexpr 2)), typ @(Var "sigma"))
            ~= (typ @Int, []),

            -- 'c' : [] :: [Char]
            [] |= (op2 'c' Cons emptyList, typ @(Var "sigma"))
            ~= (typ @[Char], []),

            -- x.hd :: v? 
            [("x", forall [] $ typ @[Var "v?"])] |=
             (expr (fd "x" [Hd def]), typ @(Var "sigma"))
            ~= (typ @(Var "v?"), []),

            -- x :: [Int] |- x.hd : x :: [Int] = 
            [("x", forall [] (typ @[Int]))] |=
             (op2 (fd "x" [Hd def]) Cons (fd "x" []), 
             typ @(Var "sigma"))
            ~= (typ @[Int], []),

            -- x :: [Int] |- x.hd : x :: [Int] = 
            [("x", forall ["a"] (typ @[Int]))] |=
             (op2 (fd "x" [Hd def]) Cons (fd "x" []),
             typ @(Var "sigma"))
            ~= (typ @[Int], []),

            -- id :: a -> a |- (id 'c') : [] :: [Char] 
            [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |=
             (op2 (fun1 "id" 'c') Cons emptyList, 
             typ @(Var "sigma"))
            ~= (typ @[Char], []),

            -- const :: a -> b -> a |- const True :: b -> Bool
            [("const", forall ["a", "b"] $ typ @(Var "a" -> Var "b" -> Var "a"))] |=
            (expr $ fun1 "const" True, typ @(Var "sigma"))
            ~= (typ @(Var "b" -> Bool), []),

            -- repl :: Int -> Char -> [Char]  |- hd (repl 3 'c') :: Char
            [("repl", forall [] $ typ @(Int -> Char -> [Char]))] |=
            (expr $ fun1 "hd" (fun2 "repl" (iexpr 3) 'c'),
             typ @(Var "sigma"))
            ~= (typ @Char, []),

            -- 'c' >= 'd' :: Bool 
            [] |= (op2 'c' GreaterEq 'd', typ @(Var "sigma")) ~= (typ @(Bool), [TOrd $ typ @Char]),

            -- x :: a |- x >= x :: Bool
            [("x", forall [] $ typ @(Var "a"))] |= 
                (op2 (fd "x" []) GreaterEq (fd "x" []), typ @(Var "sigma")) ~= (typ @(Bool), [TOrd $ typ @(Var "a")]),

            -- x :: a |- (-x) >= x :: Bool
            [("x", forall [] $ typ @(Var "a"))] |= 
                (op2 (op1 UnMinus (fd "x" [])) GreaterEq (fd "x" []), typ @(Var "sigma")) ~= (typ @Bool, [TOrd $ typ @Int]),

            -- const :: a -> b -> a |- hd (const True []) = fail
            [("const", forall ["a","b"] $ typ @(Var "a" -> Var "b" -> Var "a"))] |=
            expr (fun1 "hd" $ fun2 "const" True emptyList) ~\= typ @(Var "sigma"),

            -- x :: a |- (-x) >= (x . tl) :: ?v = fail
            [("x", forall [] $ typ @(Var "a"))] |= 
                (op2 (op1 UnMinus (fd "x" [])) GreaterEq (fd "x" [Tl def])) ~\= typ @Bool,

            -- True >= t :: ?v = Fail
            [] |= op2 True GreaterEq (iexpr 5) ~\= typ @(Var "sigma"),

            -- True <= False :: ?v = Fail
            [] |= op2 True LessEq False ~\= typ @(Var "sigma"),


            -- !('c' : []) :: ?v = Fail
            [] |= op1 UnNeg (op2 'c' Cons emptyList) ~\= typ @(Var "sigma"),
            -- !('c' : []) :: ?v = Fail
            [] |= op1 UnNeg (op2 'c' Cons emptyList) ~\= typ @(Var "sigma"),

            -- 'c' : 'd' :: ?v = Fail
            [] |= op2 'c' Cons 'd' ~\= typ @(Var "sigma"),

            -- [] :: Int = Fail
            [] |= emptyList ~\= typ @Int,

            -- 'c' + 'd' :: ?v = Fail
            [] |= op2 'c' Plus 'd' ~\= typ @(Var "sigma")
            ]

    executeTCTests tests typeCheckExpr

test_type_check_var_decl = do
    let tests = 
            [
                -- Int x = 5
                [] |= ("x", typ @Int, []) =:: iexpr 5,

                -- Char x = 'c'
                [] |= ("x", typ @Char, []) =:: expr 'c',

                -- Bool x = False 
                [] |= ("x", typ @Bool, []) =:: expr False,

                -- y :: Bool |= Bool x = y
                [("y", forall [] $ typ @Bool)] |= ("x", typ @Bool, []) =:: expr (fd "y" []),

                -- [a] x = []
                [] |= ("x", typ @[Var "a"], []) =:: emptyList,

                -- [a] x = (Bool, [])
                [] |= ("x", typ @(Bool, [Var "a"]), []) =:: expr (False, emptyList),

                -- [Int] x = (Bool, [])
                [] |= ("x", typ @(Bool, [Int]), []) =:: expr (False, emptyList),

                -- [Int] x = 5 >= 3
                [] |= ("x", typ @Bool, [TOrd $ typ @Int]) =:: op2 (iexpr 5) GreaterEq (iexpr 3),

                -- x :: a |- Var y = x == x
                [("x", forall [] $ typ @(Var "a"))] |= 
                    ("y", typ @Bool, [TEq $ typ @(Var "a")]) =:: op2 (fd "x" []) Equal (fd "x" []),

                -- id : forall a. a -> a |- (b -> b) x = id
                [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |= 
                    ("x", typ @(Var "a" -> Var "a"), []) =:: expr (fd "id" []),
                
                -- id : forall a. a -> a |- (a -> b) x = id :: fail
                [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |= 
                    ("x", typ @(Var "a" -> Var "b")) =\: expr (fd "id" []),

                -- a x = 5 :: fail
                [] |= ("x", typ @(Var "a")) =\: iexpr 5 
            ]

    executeTCTests tests (\e v _ -> typeCheckVarDecl e v)


test_type_check_stmt = do
    let tests = 
            [
                -- if True { return False } else { return True } :: Bool
                [] |= (ite True [ret False] [ret True], typ @(Var "a")) ~= (typ @Bool, []),

                -- if True {} :: ?a
                [] |= (ite True [] [], typ @(Var "a")) ~= (typ @(Var "a"), []),

                -- if True { print(x == x); } :: ?a
                [("x", forall [] $ typ @(Var "a"))] |= 
                    (ite True [stmt $ fun1 "print" (op2 (fd "x" []) Nequal (fd "x" []))] 
                              [], typ @(Var "a")) 
                    ~= (typ @(Var "a"), [TPrint $ typ @Bool, TEq $ typ @(Var "a")]),

                -- id :: forall a. a -> a |- if True { print(x == x); } else { id(x >= 5) } :: ?a, [Print Bool, Eq Int, Ord Int]
                [("x", forall [] $ typ @(Var "a")), ("id", forall ["b"] $ typ @(Var "b" -> Var "b"))] |= 
                    (ite True [stmt $ fun1 "print" (op2 (fd "x" []) Nequal (fd "x" []))] 
                              [stmt $ fun1 "id" (op2 (fd "x" []) GreaterEq (iexpr 5))], typ @(Var "b")) 
                    ~= (typ @(Var "b"), [TPrint $ typ @Bool, TEq $ typ @Int, TOrd $ typ @Int]),

                -- if True { return [False] } else { return [True] } :: [Bool]
                [] |= (ite True [ret [False]] [ret [True]], typ @[Var "a"]) ~= (typ @[Bool], []),

                -- if True { return [] } else { return [] } :: [Int]
                [] |= (ite True [ret emptyList] [ret emptyList], typ @[Int]) ~= (typ @[Int], []),

                -- while (True) { return [] } :: [?a]
                [] |= (while True [ret emptyList], typ @(Var "a")) ~= (typ @[Var "b"], []),
                
                -- while (True) { print (5); return [] } :: [?a], Printable Int
                [] |= (while True [stmt $ fun1 "print" (iexpr 5), ret emptyList], typ @(Var "a")) 
                    ~= (typ @[Var "b"], [TPrint $ typ @Int]),

                -- x : a |- while (True) { x = 5; return x; } :: Int
                [("x", forall [] $ typ @(Var "a"))] |= 
                    (while True [ fd "x" [] =: iexpr 5, ret (fd "x" [])], typ @(Var "b")) ~= (typ @Int, []),

                -- id : forall a. a -> a |- while (True) { id(5); return id; } :: b -> b
                [("id", forall ["a"] $ typ @(Var "a" -> Var "a"))] |= 
                    (while True [ stmt (fun1 "id" (iexpr 5)), ret (fd "id" []) ], typ @(Var "b")) 
                                ~= (typ @(Var "c" -> Var "c"), []),
                
                -- x : [a] |- while (True) { x = []; x.hd = 3; return x; } :: [Int]
                [("x", forall [] $ typ @[Var "a"])] |= 
                (while True [ fd "x" [] =: emptyList, 
                              fd "x" [Hd def] =: iexpr 3, 
                              ret (fd "x" []) ], typ @(Var "b")) ~= (typ @[Int], []),

                -- x : [[(a,b)]] |- while (True) { x.tl.hd.fst = 3; return x; } :: [[(Int, b)]]
                [("x", forall [] $ typ @[[(Var "a", Var "b")]])] |= 
                (while True [ fd "x" [Tl def, Hd def, Hd def, Fst def] =: iexpr 3, 
                              ret (fd "x" []) ], typ @(Var "c")) ~= (typ @[[(Int, Var "b")]], []),

                -- while (True) { return True; return; } fail
                [] |= while True [ ret True, retVoid ] ~\= typ @(Var "b"),
                
                -- while ('c') { return True; } :: fail
                [] |= while 'c' [ ret True ] ~\= typ @(Var "a"),

                -- if (5) { return False } { return True } fail
                [] |= ite (iexpr 5) [ret False] [ret True] ~\= typ @(Var "a"),

                -- if (True) { return False } { return 5 } fail
                [] |= ite (True) [ret False] [ret (iexpr 5)] ~\= typ @(Var "a")
            ]

    executeTCTests tests typeCheckStmt

test_type_check_fun_decl = do
    let tests = 
            [
                -- id (x) :: b -> b { return x; } :: a -> a
                [] |= declare "id" ["x"] (typ @(Var "b" -> Var "b")) 
                                    [ ] [ ret (fd "x" []) ] .:: (typ @(Var "a" -> Var "a"), []),

                -- foo (x) :: Int -> Bool { var z = x != 5; return z; } :: Bool -> Int, TEq Int
                [] |= declare "foo" ["x"] (typ @(Int -> Bool)) 
                                    [ defineI "z" (op2 (fd "x" []) Nequal (iexpr 5)) ] 
                                    [ ret (fd "z" []) ] .:: (typ @(Int -> Bool), [TEq $ typ @Int]),

                -- foo (x) :: Int -> Int { var y = x + 5; return y; } :: Int -> Int
                [] |= declare "foo" ["x"] (typ @(Int -> Int)) 
                                    [ defineI "y" (op2 (fd "x" []) Plus (iexpr 5)) ] 
                                    [ ret (fd "y" []) ] .:: (typ @(Int -> Int), []),

                -- fact (x) :: Int -> Int { Var r = x * fact(x - 1); return r; } :: Int -> Int
                [] |= declare "fact" ["x"] (typ @(Int -> Int)) 
                                    [ defineI "r" (op2 (fd "x" []) Mul (fun1 "fact" (op2 (fd "x" []) Minus (iexpr 1)))) ] 
                                    [ ret (fd "r" []) ] .:: (typ @(Int -> Int), []),

                -- infId (x) :: a -> a { Var z = weirdId(x); return x; } :: a -> a
                [] |= declare "weirdId" ["x"] (typ @(Var "a" -> Var "a")) 
                                            [defineI "z" (expr $ fun1 "weirdId" (fd "x" []))]
                                            [ ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "a"), []),

                -- -- idPrint (x) :: a -> a { print(x); return x; }; :: a -> a, Print a
                -- [] |= declare "idPrint" ["x"] (typ @(Var "a" -> Var "a")) 
                --                             []
                --                             [ stmt $ fun1 "print" (fd "x" []), ret (fd "x" []) ] 
                --                             .:: (typ @(Var "a" -> Var "a"), [TPrint $ typ @(Var "a")]),

                -- constPrint (x, y) :: a -> b -> a { print(y); return x; } } :: a -> b -> a
                [] |= declare "constPrint" ["x", "y"] (typ @(Var "a" -> Var "b" -> Var "a")) 
                                            []
                                            [ stmt (fun1 "print" (fd "y" [])),  ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "b" -> Var "a"), []),

                -- constPrint (x, y) :: a -> b -> a { print(y); return x; } } :: a -> b -> a
                [] |= declare "constPrint" ["x", "y"] (typ @(Var "a" -> Var "b" -> Var "a")) 
                                            []
                                            [ stmt (fun1 "print" (fd "y" [])),  ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "b" -> Var "a"), []),
                -- constPrint (x, y) :: a -> a -> a { return x; } } :: a -> a -> a
                [] |= declare "constPrint" ["x", "y"] (typ @(Var "a" -> Var "a" -> Var "a")) 
                                            []
                                            [ ret (fd "x" []) ] 
                                            .:: (typ @(Var "a" -> Var "a" -> Var "a"), []),

                -- constPrint (x, y) :: a -> b -> b { return x; } } :: a -> b -> a
                [] |= failure (declare "constPrint" ["x", "y"] (typ @(Var "a" -> Var "b" -> Var "b")) 
                                                    []
                                                    [ ret (fd "x" []) ] ),

                -- invalidId (x) :: a -> a { Var z = invalidId(5); return x; } :: a -> a
                [] |= failure (declare "invalidId" ["x"] (typ @(Var "a" -> Var "a")) 
                                            [defineI "z" (expr $ fun1 "invalidId" (iexpr 5))]
                                            [ ret (fd "x" []) ])
            ]

    executeTCTests tests (\e v _ -> (\(x@(TCTFunDecl _ _ _ t _),y) -> (getTypeCon t, x, y)) <$> typeCheckFunDecl e v)
