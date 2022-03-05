{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE FlexibleContexts #-}

module SPL.Compiler.Parser.Test (htf_SPL_Compiler_Parser_Test_thisModulesTests) where

import Test.Framework hiding (Testable)
import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..), Type(..), Keyword(..))
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..))
import SPL.Compiler.Parser.ASTParser (pType, pFargs, pFunType, pExpr, pTupExpr, pStmt)
import SPL.Compiler.Parser.AST
import SPL.Compiler.Parser.ASTEntityLocation
import qualified Data.ByteString.Lazy as B
import Data.Text (Text)
import Data.Default
import Control.Monad (forM_)
import Control.Applicative ((<|>))
import Control.Lens ((^..), (^?), _Right, ix, _1)

instance Default EntityLoc where
    def = EntityLoc (1,1) (1,1)

instance Default AlexPosn where
    def = AlexPn 0 1 1

-- used for test purposes
-- transform a data type to its test form
-- this means that certain fields may be replaced
-- with their default values for ease of comparisons, etc.
class Testable a where
    toTestForm :: a -> a

instance Testable ASTIdentifier where
    toTestForm (ASTIdentifier _ i) = ASTIdentifier def i

instance Testable ASTFunCall where
    toTestForm (ASTFunCall _ i e) = ASTFunCall def (toTestForm i) (toTestForm e)

instance Testable ASTType where
    toTestForm (ASTUnknownType l) = ASTUnknownType def
    toTestForm (ASTFunType _ t) = ASTFunType def (toTestForm t)
    toTestForm (ASTTupleType _ t1 t2) = ASTTupleType def (toTestForm t1) (toTestForm t2)
    toTestForm (ASTListType _ t) = ASTListType def (toTestForm t)
    toTestForm (ASTVarType _ v) = ASTVarType def v
    toTestForm (ASTIntType _) = ASTIntType def
    toTestForm (ASTBoolType _) = ASTBoolType def
    toTestForm (ASTCharType _) = ASTCharType def
    toTestForm (ASTVoidType _) = ASTVoidType def

instance Testable ASTExpr where
    toTestForm (TupExpr _ p1 p2) = TupExpr def (toTestForm p1) (toTestForm p2)
    toTestForm (FunCallExpr c) = FunCallExpr (toTestForm c)
    toTestForm (IdentifierExpr i) = IdentifierExpr (toTestForm i)
    toTestForm (IntExpr _ i) = IntExpr def i
    toTestForm (CharExpr _ c) = CharExpr def c
    toTestForm (BoolExpr _ b) = BoolExpr def b
    toTestForm (OpExpr _ o e) = OpExpr def o (toTestForm e)
    toTestForm (Op2Expr _ e1 o e2) = Op2Expr def (toTestForm e1) o (toTestForm e2)
    toTestForm (EmptyListExpr _ ) = EmptyListExpr def

instance Testable a => Testable [a] where
    toTestForm = map toTestForm

instance Testable ASTStmt where
    toTestForm (IfElseStmt _ val1 val2 val3) = IfElseStmt def (toTestForm val1) (toTestForm val2) (toTestForm val3)
    toTestForm (WhileStmt _ val1 val2) = WhileStmt def (toTestForm val1) (toTestForm val2)
    toTestForm (AssignStmt _ val1 val2) = AssignStmt def (toTestForm val1) (toTestForm val2)
    toTestForm (FunCallStmt _ val1) = FunCallStmt def (toTestForm val1)
    toTestForm (ReturnStmt _ val1) = ReturnStmt def (toTestForm val1)

instance Testable a => Testable (Maybe a) where
    toTestForm (Just val) = Just (toTestForm val)
    toTestForm Nothing = Nothing


executeMultipleTests :: (Testable b, Eq b, Show b) => Parser Token Text b -> [([SPLToken], Maybe b)] -> IO ()
executeMultipleTests parser tests =
    forM_ tests $ \(input, expected) -> do
        let tokens = map mkToken input
        let actual = runParser parser (ParserState 0 tokens)
        case expected of
            Just value -> do
                let a = toTestForm <$> actual ^? ix 0. _Right. _1
                assertEqual (Just $ toTestForm value) a
            _ -> mapM_ (\e -> print e >> assertLeft e) (runParser parser (ParserState 0 tokens))

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
                            (FunCallExpr $ ASTFunCall def (ASTIdentifier def "fst") [IdentifierExpr (ASTIdentifier def "p1")])
                            Plus
                            (FunCallExpr $ ASTFunCall def (ASTIdentifier def "fst") [IdentifierExpr (ASTIdentifier def "p2")])
                        )
                        (Op2Expr def
                            (FunCallExpr $ ASTFunCall def (ASTIdentifier def "snd") [IdentifierExpr (ASTIdentifier def "p1")])
                            Minus
                            (FunCallExpr $ ASTFunCall def (ASTIdentifier def "snd") [IdentifierExpr (ASTIdentifier def "p2")])
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
                            (FunCallExpr
                                (ASTFunCall def (ASTIdentifier def "fst") [IdentifierExpr (ASTIdentifier def "p1")])
                            )
                            Plus
                            (FunCallExpr
                                (ASTFunCall def (ASTIdentifier def "fst") [IdentifierExpr (ASTIdentifier def "p2")])
                            )
                        )
                        (TupExpr def
                            (Op2Expr def
                                (FunCallExpr
                                    (ASTFunCall def (ASTIdentifier def "fst")
                                        [FunCallExpr (ASTFunCall def (ASTIdentifier def "snd") [IdentifierExpr (ASTIdentifier def "p1")])]
                                    )
                                )
                            Div
                            (FunCallExpr
                                (ASTFunCall def (ASTIdentifier def "fst")
                                            [FunCallExpr (ASTFunCall def (ASTIdentifier def "snd") [IdentifierExpr (ASTIdentifier def "p2")])]
                                )
                            ))
                            (Op2Expr def
                                (FunCallExpr (ASTFunCall def (ASTIdentifier def "snd")
                                    [FunCallExpr (ASTFunCall def (ASTIdentifier def "snd") [IdentifierExpr (ASTIdentifier def "p1")])])
                                )
                            Mul
                            (FunCallExpr
                                (ASTFunCall def (ASTIdentifier def "snd")
                                    [FunCallExpr (ASTFunCall def (ASTIdentifier def "snd") [IdentifierExpr (ASTIdentifier def "p2")])])
                            ))
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
                (IdentifierExpr (ASTIdentifier def "tempDay")) 
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
                   (FunCallExpr (ASTFunCall def (ASTIdentifier def "hd") [IdentifierExpr (ASTIdentifier def "list")]))
                   LogOr (FunCallExpr
                        (ASTFunCall def (ASTIdentifier def "sum")
                             [ FunCallExpr
                                   (ASTFunCall def (ASTIdentifier def "tl")
                                        [ IdentifierExpr (ASTIdentifier def "list") ])
                             ]
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
                   (FunCallExpr
                        (ASTFunCall def (ASTIdentifier def "hd") [IdentifierExpr (ASTIdentifier def "list")]))
                   LogAnd
                   (FunCallExpr
                        (ASTFunCall def (ASTIdentifier def "sum")
                             [ FunCallExpr
                                   (ASTFunCall def (ASTIdentifier def "tl")
                                        [ IdentifierExpr (ASTIdentifier def "list") ])
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
                   (Op2Expr def (IdentifierExpr (ASTIdentifier def "facN"))
                        Nequal
                        (FunCallExpr
                             (ASTFunCall def (ASTIdentifier def "facI")
                                  [IdentifierExpr (ASTIdentifier def "n")])))
                   LogOr
                   (Op2Expr def (IdentifierExpr (ASTIdentifier def "facN"))
                        Nequal
                        (FunCallExpr
                             (ASTFunCall def (ASTIdentifier def "facL")
                                  [IdentifierExpr (ASTIdentifier def "n")])
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
                                    [IdentifierExpr (ASTIdentifier def "list")]))
                        )
                )
                LogAnd
                (Op2Expr def
                     (Op2Expr def
                          (FunCallExpr
                               (ASTFunCall def (ASTIdentifier def "hd")
                                    [ IdentifierExpr (ASTIdentifier def "list") ]))
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
                FunCallExpr
                     (ASTFunCall def
                          (ASTIdentifier def "fst")
                          [ FunCallExpr (ASTFunCall def
                                     (ASTIdentifier def "f")
                                     [ TupExpr def
                                           (IdentifierExpr (ASTIdentifier def "x"))
                                           (IdentifierExpr (ASTIdentifier def "x"))
                                     ])
                          ]
                     )
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
            --> AssignStmt def (ASTIdentifier def "a") (IdentifierExpr (ASTIdentifier def "b")),
            -- if (3 == x) {function();} else {return;}
            [KeywordToken If,SymbolToken '(',IntToken 3,SymbolToken '=',SymbolToken '=',IdentifierToken "x",SymbolToken ')'
            ,SymbolToken '{',IdentifierToken "function",SymbolToken '(',SymbolToken ')',SymbolToken ';',SymbolToken '}'
            ,KeywordToken Else,SymbolToken '{',KeywordToken Return,SymbolToken ';',SymbolToken '}']
            --> IfElseStmt def (Op2Expr def (IntExpr def 3) Equal (IdentifierExpr (ASTIdentifier def "x")))
                    [FunCallStmt def (ASTFunCall def (ASTIdentifier def "function") [])] [ReturnStmt def Nothing],
            -- if (isEmpty(a) && isEmpty(b)) { return True; }
            [KeywordToken If, SymbolToken '(', IdentifierToken "isEmpty", SymbolToken '(',
             IdentifierToken "a", SymbolToken ')', SymbolToken '&', SymbolToken '&',
             IdentifierToken "isEmpty", SymbolToken '(', IdentifierToken "b", SymbolToken ')', SymbolToken ')',
             SymbolToken '{', KeywordToken Return, BoolToken True, SymbolToken ';', SymbolToken '}']
             --> IfElseStmt def 
                    (Op2Expr def 
                        (FunCallExpr (ASTFunCall def (ASTIdentifier def "isEmpty") [IdentifierExpr (ASTIdentifier def "a")]))
                        LogAnd
                        (FunCallExpr (ASTFunCall def (ASTIdentifier def "isEmpty") [IdentifierExpr (ASTIdentifier def "b")]))
                    )
                    [ ReturnStmt def $ Just (BoolExpr def True) ]
                    []
            ]
    executeMultipleTests pStmt tests
