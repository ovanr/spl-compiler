{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE FlexibleContexts #-}

module SPL.Compiler.Parser.Test (htf_SPL_Compiler_Parser_Test_thisModulesTests) where

import Test.Framework hiding (Testable)
import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..), Type(..), Keyword(..))
import SPL.Compiler.Parser.ParserCombinator (Parser(..), ParserState(..))
import SPL.Compiler.Parser.ASTParser (pType, pFargs, pFunType, pExpr, pTupExpr)
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
    toTestForm a = a

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
            [TypeToken IntType] --> ASTIntType,
            [TypeToken BoolType] --> ASTBoolType,
            [TypeToken CharType] --> ASTCharType,
            [IdentifierToken "a"] --> ASTVarType "a",
            [ SymbolToken '(', IdentifierToken "b", SymbolToken ',', TypeToken IntType, SymbolToken ')']
                --> ASTTupleType (ASTVarType "b") ASTIntType,
            [SymbolToken '[', IdentifierToken "b", SymbolToken ']'] --> ASTListType (ASTVarType "b"),
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
                --> ASTFunType [ASTIntType],
            [SymbolToken ':', SymbolToken ':', TypeToken IntType, IdentifierToken "a", SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTVarType "a", ASTCharType],
            [SymbolToken ':', SymbolToken ':', TypeToken IntType, IdentifierToken "a", SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTVarType "a", ASTCharType],
            [SymbolToken ':', SymbolToken ':', TypeToken IntType, SymbolToken '[', IdentifierToken "a", SymbolToken ']', SymbolToken '-', SymbolToken '>', TypeToken CharType]
                --> ASTFunType [ASTIntType, ASTListType (ASTVarType "a"), ASTCharType],
            failure [SymbolToken ':', SymbolToken ':', SymbolToken '-', SymbolToken '>', SymbolToken '{'],
            failure [SymbolToken ':', SymbolToken ':', TypeToken CharType]
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

            -- ((p1.fst + p2.fst), (p1.snd.fst + p2.snd.fst, p1.snd.snd + p2.snd.snd))
            [SymbolToken '(',
                SymbolToken '(',
                    IdentifierToken "p1", SymbolToken '.', IdentifierToken "fst", SymbolToken '+',
                    IdentifierToken "p2", SymbolToken '.', IdentifierToken "fst",
                SymbolToken ')',
                SymbolToken ',',
                SymbolToken '(',
                    IdentifierToken "p1", SymbolToken '.', IdentifierToken "snd",
                                          SymbolToken '.', IdentifierToken "fst", SymbolToken '+',
                    IdentifierToken "p2", SymbolToken '.', IdentifierToken "snd",
                                          SymbolToken '.', IdentifierToken "fst",
                    SymbolToken ',',
                    IdentifierToken "p1", SymbolToken '.', IdentifierToken "snd",
                                          SymbolToken '.', IdentifierToken "snd", SymbolToken '+',
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
                            Plus
                            (FunCallExpr
                                (ASTFunCall def (ASTIdentifier def "fst")
                                            [FunCallExpr (ASTFunCall def (ASTIdentifier def "snd") [IdentifierExpr (ASTIdentifier def "p2")])]
                                )
                            ))
                            (Op2Expr def
                                (FunCallExpr (ASTFunCall def (ASTIdentifier def "snd")
                                    [FunCallExpr (ASTFunCall def (ASTIdentifier def "snd") [IdentifierExpr (ASTIdentifier def "p1")])])
                                )
                            Plus
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



