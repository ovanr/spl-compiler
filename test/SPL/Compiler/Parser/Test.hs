{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE FlexibleContexts #-}

module SPL.Compiler.Parser.Test (htf_SPL_Compiler_Parser_Test_thisModulesTests) where

import Test.Framework hiding (Testable)
import qualified Data.ByteString.Lazy as B
import Data.Text (Text)
import Data.Default
import Control.Monad (forM_)
import Control.Applicative ((<|>))
import Control.Lens ((^..), (^?), _Right, ix, _1, folded)

import SPL.Compiler.Parser.Testable
import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..), Type(..), Keyword(..))
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..))
import SPL.Compiler.Parser.ASTParser (pType, pFargs, pFunType, pExpr, pTupExprOrParens, pStmt, pVarDecl, pFunDecl)
import SPL.Compiler.Parser.AST
import SPL.Compiler.Parser.ASTEntityLocation


executeMultipleTests :: (Testable b, Eq b, Show b) => Parser Token [Text] b -> [([SPLToken], Maybe b)] -> IO ()
executeMultipleTests parser tests =
    forM_ tests $ \(input, expected) -> do
        let tokens = map mkToken input
        let actual = runParser parser (ParserState 0 tokens mempty mempty)
        case expected of
            Just value -> do
                let a = toTestForm <$> actual ^? folded._Right._1
                assertEqual (Just $ toTestForm value) a
            _ -> mapM_ (\e -> print e >> assertLeft e) (runParser parser (ParserState 0 tokens mempty mempty))

-- Shorthand operator to create an (input, expected output) pair
infixl 1 -->
(-->) :: a -> b -> (a, Maybe b)
input --> expected = (input, Just expected)

mkToken :: SPLToken -> Token
mkToken = MkToken def

failure :: a -> (a, Maybe b)
failure input = (input, Nothing)

test_parse_type = do
    let tests = [
            [TypeToken IntType] --> ASTIntType def,
            [TypeToken BoolType] --> ASTBoolType def,
            [TypeToken CharType] --> ASTCharType def,
            [IdentifierToken "a"] --> ASTVarType def "a",
            [ SymbolToken '(', IdentifierToken "b", SymbolToken ',', TypeToken IntType, SymbolToken ')']
                --> ASTTupleType def (ASTVarType def "b") (ASTIntType def),
            [SymbolToken '[', IdentifierToken "b", SymbolToken ']'] --> ASTListType def (ASTVarType def "b"),
            failure [SymbolToken '[', IdentifierToken "b", TypeToken IntType, SymbolToken ']'],
            failure [SymbolToken '(', IdentifierToken "b", TypeToken IntType, SymbolToken ')']
            ]
    executeMultipleTests pType tests

test_parse_fargs = do
    let tests = [
            [IdentifierToken "a", SymbolToken ',', IdentifierToken "b"]
                --> [ASTIdentifier def "a", ASTIdentifier def "b"],
            [IdentifierToken "a"] --> [ASTIdentifier def "a"],
            [] --> [],
            [IdentifierToken "a", SymbolToken ','] --> [],
            [KeywordToken Var] --> []
            ]
    executeMultipleTests pFargs tests

test_parse_ftype = do
    let tests = [
            [SymbolToken ':', SymbolToken ':', SymbolToken '-', SymbolToken '>', TypeToken IntType]
                --> ASTFunType def [ASTIntType def],
            [SymbolToken ':', SymbolToken ':',
                TypeToken IntType, IdentifierToken "a",
                SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType def [ASTIntType def, ASTVarType def "a", ASTCharType def],
            [SymbolToken ':', SymbolToken ':',
                TypeToken IntType, IdentifierToken "a",
                SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType def [ASTIntType def, ASTVarType def "a", ASTCharType def],
            [SymbolToken ':', SymbolToken ':',
                TypeToken IntType, SymbolToken '[', IdentifierToken "a", SymbolToken ']',
                SymbolToken '-', SymbolToken '>',
                TypeToken CharType
            ] --> ASTFunType def [ASTIntType def, ASTListType def (ASTVarType def "a"), ASTCharType def],
            [SymbolToken ':', SymbolToken ':', SymbolToken '-', SymbolToken '>', SymbolToken '{'] 
                --> ASTUnknownType def,
            [SymbolToken ':', SymbolToken ':', TypeToken CharType]
                --> ASTUnknownType def
            ]
    executeMultipleTests pFunType tests

test_parse_pexpr_tuple = do
    let tests = [
            -- (2, 2)
            [SymbolToken '(', IntToken 2, SymbolToken ',', IntToken 2, SymbolToken ')']
                --> TupExpr def (IntExpr def 2) (IntExpr def 2),
           -- ((p1.fst + p2.fst), (p1.snd - p2.snd))
           [SymbolToken '(',
               SymbolToken '(',
                   IdentifierToken "p1", SymbolToken '.', IdentifierToken "fst", SymbolToken '+',
                   IdentifierToken "p2", SymbolToken '.', IdentifierToken "fst",
               SymbolToken ')', SymbolToken ',', SymbolToken '(',
                   IdentifierToken "p1", SymbolToken '.', IdentifierToken "snd", SymbolToken '-',
                   IdentifierToken "p2", SymbolToken '.', IdentifierToken "snd", SymbolToken ')',
               SymbolToken ')',
           SymbolToken ')']
               --> TupExpr def
                       (Op2Expr def
                           (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p1") [Fst def]))
                           Plus
                           (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p2") [Fst def]))
                       )
                       (Op2Expr def
                           (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p1") [Snd def]))
                           Minus
                           (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p2") [Snd def]))
                       ),

           -- ((p1.fst + p2.fst), (p1.snd.fst / p2.snd.fst, p1.snd.snd * p2.snd.snd))
           [SymbolToken '(',
               SymbolToken '(',
                   IdentifierToken "p1", SymbolToken '.', IdentifierToken "fst", SymbolToken '+',
                   IdentifierToken "p2", SymbolToken '.', IdentifierToken "fst",
               SymbolToken ')',
               SymbolToken ',',
               SymbolToken '(',
                   IdentifierToken "p1", SymbolToken '.', IdentifierToken "snd",
                                         SymbolToken '.', IdentifierToken "fst", SymbolToken '/',
                   IdentifierToken "p2", SymbolToken '.', IdentifierToken "snd",
                                         SymbolToken '.', IdentifierToken "fst",
                   SymbolToken ',',
                   IdentifierToken "p1", SymbolToken '.', IdentifierToken "snd",
                                         SymbolToken '.', IdentifierToken "snd", SymbolToken '*',
                   IdentifierToken "p2", SymbolToken '.', IdentifierToken "snd",
                                         SymbolToken '.', IdentifierToken "snd",
               SymbolToken ')',
           SymbolToken ')']
               --> TupExpr def
                       (Op2Expr def
                           (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p1") [Fst def]))
                           Plus
                           (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p2") [Fst def]))
                       )
                       (TupExpr def
                           (Op2Expr def
                               (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p1") [Snd def, Fst def]))
                           Div
                               (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p2") [Snd def, Fst def]))
                           )
                           (Op2Expr def
                               (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p1") [Snd def, Snd def]))
                           Mul
                               (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "p2") [Snd def, Snd def]))
                           )
                       )
                ]
    executeMultipleTests pExpr tests

test_parse_pexpr_list = do
    let tests = [
            -- 3:[]
            [IntToken 3,SymbolToken ':',SymbolToken '[',SymbolToken ']']
                --> Op2Expr def (IntExpr def 3) Cons (EmptyListExpr def),
            -- 'h':'e':'l':'l':'o':[]
            [CharToken 'h',SymbolToken ':',CharToken 'e',SymbolToken ':',CharToken 'l',SymbolToken ':',
             CharToken 'l',SymbolToken ':',CharToken 'o',SymbolToken ':',SymbolToken '[',SymbolToken ']']
                --> Op2Expr def (CharExpr def 'h')
                    Cons (Op2Expr def (CharExpr def 'e')
                        Cons (Op2Expr def (CharExpr def 'l')
                            Cons (Op2Expr def (CharExpr def 'l')
                                Cons (Op2Expr def (CharExpr def 'o')
                                    Cons (EmptyListExpr def)))))
                ]

    executeMultipleTests pExpr tests

test_parse_pexpr_complex = do
    let tests =
            [ 
              -- tempDay ----getIndex()
              [ IdentifierToken "tempDay", SymbolToken '-', SymbolToken '-', SymbolToken '-', SymbolToken '-',
                IdentifierToken "getIndex", SymbolToken '(', SymbolToken ')'
              ] -->
              Op2Expr def 
                (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "tempDay") [])) 
                Minus 
                (OpExpr def UnMinus 
                    (OpExpr def UnMinus 
                        (OpExpr def UnMinus 
                            (FunCallExpr (ASTFunCall def (ASTIdentifier def "getIndex") []))
                        )
                    )
                ),
            -- list.hd || sum(list.tl)
            [ IdentifierToken "list" , SymbolToken '.' , IdentifierToken "hd" ,
                SymbolToken '|' , SymbolToken '|' ,
                IdentifierToken "sum" ,
                SymbolToken '(' ,
                    IdentifierToken "list" , SymbolToken '.' , IdentifierToken "tl" ,
                SymbolToken ')'
              ] -->
              Op2Expr def
                   (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "list") [Hd def]))
                   LogOr (FunCallExpr
                        (ASTFunCall def (ASTIdentifier def "sum")
                             [ FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "list") [Tl def] ) ]
                        ))

            -- list.hd && sum(list.tl)
            , [ IdentifierToken "list" , SymbolToken '.' , IdentifierToken "hd"
              , SymbolToken '&' , SymbolToken '&'
              , IdentifierToken "sum"
              , SymbolToken '('
              , IdentifierToken "list" , SymbolToken '.' , IdentifierToken "tl"
              , SymbolToken ')'
              ] -->
              Op2Expr def
                   (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "list") [Hd def]))
                   LogAnd
                   (FunCallExpr
                        (ASTFunCall def (ASTIdentifier def "sum")
                             [ 
                                FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "list") [Tl def])
                             ]
                        )
                   )

            -- ( facN != facI ( n ) || facN != facL ( n ))
            , [ SymbolToken '('
              , IdentifierToken "facN" , SymbolToken '!' , SymbolToken '='
              , IdentifierToken "facI" , SymbolToken '(' , IdentifierToken "n" , SymbolToken ')'
              , SymbolToken '|' , SymbolToken '|'
              , IdentifierToken "facN"
              , SymbolToken '!' , SymbolToken '='
              , IdentifierToken "facL" , SymbolToken '(' , IdentifierToken "n" , SymbolToken ')'
              , SymbolToken ')'
              ] -->
              Op2Expr def
                   (Op2Expr def 
                        (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "facN") []))
                        Nequal
                        (FunCallExpr
                             (ASTFunCall def (ASTIdentifier def "facI")
                                  [FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "n") [])]
                             )
                        )
                   )
                   LogOr
                   (Op2Expr def 
                        (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "facN") []))
                        Nequal
                        (FunCallExpr
                             (ASTFunCall def (ASTIdentifier def "facL")
                                  [FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "n") [])]
                            )
                        )
                   )

            -- ! ! isEmpty (list) && list.hd % 2 == 0
            , [ SymbolToken '!', SymbolToken '!'
              , IdentifierToken "isEmpty" , SymbolToken '(' , IdentifierToken "list" , SymbolToken ')'
              , SymbolToken '&' , SymbolToken '&'
              , IdentifierToken "list" , SymbolToken '.' , IdentifierToken "hd"
              , SymbolToken '%' , IntToken 2
              , SymbolToken '=' , SymbolToken '=' , IntToken 0
              ] -->
              Op2Expr def
                (OpExpr def
                   UnNeg
                        (OpExpr def
                            UnNeg
                            (FunCallExpr
                                 (ASTFunCall def (ASTIdentifier def "isEmpty")
                                    [FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "list") [])]
                                 )
                            )
                        )
                )
                LogAnd
                (Op2Expr def
                     (Op2Expr def
                         (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "list") [Hd def]))
                          Mod
                          (IntExpr def 2))
                     Equal
                     (IntExpr def 0)
                ),

            -- f((x, x)).fst
            [ IdentifierToken "f" , SymbolToken '('
            , SymbolToken '(' , IdentifierToken "x" , SymbolToken ',' , IdentifierToken "x"
            , SymbolToken ')' , SymbolToken ')'
            , SymbolToken '.' , IdentifierToken "fst"
            ] -->
                           FunCallExpr (ASTFunCall def
                                     (ASTIdentifier def "f")
                                     [ TupExpr def
                                           (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "x") []))
                                           (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "x") []))
                                     ])
            ]
    executeMultipleTests pExpr tests

test_parse_stmts = do
    let tests = 
            [
            -- foo();
            [IdentifierToken "foo",SymbolToken '(',SymbolToken ')',SymbolToken ';']
            --> FunCallStmt def (ASTFunCall def (ASTIdentifier def "foo") []),
            -- return;
            [KeywordToken Return, SymbolToken ';']
            --> ReturnStmt def Nothing,
            -- while (True) {return;}
            [KeywordToken While,SymbolToken '(',BoolToken True,SymbolToken ')'
            ,SymbolToken '{',KeywordToken Return,SymbolToken ';',SymbolToken '}']
            --> WhileStmt def (BoolExpr def True) [ReturnStmt def Nothing],
            -- a = b;
            [IdentifierToken "a",SymbolToken '=',IdentifierToken "b",SymbolToken ';']
            --> AssignStmt def (ASTFieldSelector def (ASTIdentifier def "a") []) 
                    (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "b") [])),
            -- if (3 == x) {function();} else {return;}
            [KeywordToken If,SymbolToken '(',IntToken 3,SymbolToken '=',SymbolToken '=',IdentifierToken "x",SymbolToken ')'
            ,SymbolToken '{',IdentifierToken "function",SymbolToken '(',SymbolToken ')',SymbolToken ';',SymbolToken '}'
            ,KeywordToken Else,SymbolToken '{',KeywordToken Return,SymbolToken ';',SymbolToken '}']
            --> IfElseStmt def (Op2Expr def (IntExpr def 3) Equal (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "x") [])))
                    [FunCallStmt def (ASTFunCall def (ASTIdentifier def "function") [])] [ReturnStmt def Nothing],
            -- if (isEmpty(a) && isEmpty(b)) { return True; }
            [KeywordToken If, SymbolToken '(', IdentifierToken "isEmpty", SymbolToken '(',
             IdentifierToken "a", SymbolToken ')', SymbolToken '&', SymbolToken '&',
             IdentifierToken "isEmpty", SymbolToken '(', IdentifierToken "b", SymbolToken ')', SymbolToken ')',
             SymbolToken '{', KeywordToken Return, BoolToken True, SymbolToken ';', SymbolToken '}']
             --> IfElseStmt def 
                    (Op2Expr def 
                        (FunCallExpr (ASTFunCall def (ASTIdentifier def "isEmpty") 
                            [FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "a") [])]))
                        LogAnd
                        (FunCallExpr (ASTFunCall def (ASTIdentifier def "isEmpty") 
                            [FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "b") [])]))
                    )
                    [ ReturnStmt def $ Just (BoolExpr def True) ]
                    []
            ]
    executeMultipleTests pStmt tests


test_parser_var_decl = do
    let tests = 
            [
            -- var x = y;
            [KeywordToken Var, IdentifierToken "x", SymbolToken '=', IdentifierToken "y", SymbolToken ';']
                --> ASTVarDecl def (ASTUnknownType def) 
                                   (ASTIdentifier def "x") 
                                   (FieldSelectExpr (ASTFieldSelector def (ASTIdentifier def "y") []))
            ,
            -- [Int] dcLengthOfMonth = 0 : 31 : [];
            [SymbolToken '[', TypeToken IntType, SymbolToken ']', IdentifierToken "dcLengthOfMonth",
             SymbolToken '=', IntToken 0, SymbolToken ':', IntToken 31, SymbolToken ':', SymbolToken '[', SymbolToken ']', SymbolToken ';']
                --> 
                ASTVarDecl def 
                    (ASTListType def (ASTIntType def)) 
                    (ASTIdentifier def "dcLengthOfMonth") 
                    (Op2Expr def 
                        (IntExpr def 0) 
                        Cons 
                        (Op2Expr def 
                            (IntExpr def 31) 
                            Cons 
                            (EmptyListExpr def)
                        )
                    )
            ]
    executeMultipleTests pVarDecl tests

test_parser_fun_decl = do
    let tests = []
    executeMultipleTests pFunDecl tests
