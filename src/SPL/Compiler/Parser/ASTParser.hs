{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module SPL.Compiler.Parser.ASTParser where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..)) 
import qualified SPL.Compiler.Lexer.AlexLexGen as Lex (Keyword(..), Type(..))
import SPL.Compiler.Parser.ParserCombinator
import SPL.Compiler.Parser.AST 
import SPL.Compiler.Parser.ASTEntityLocation
import Control.Applicative
import Control.Lens ((%~), _1, _2)
import qualified Data.Text as T
import Data.Text (Text)
import Data.Functor (($>))
import Data.Function ((&))
import Data.Maybe (maybeToList)

pParens :: Parser Token Text a -> Parser Token Text a
pParens p = pIsSymbol '(' *> p <* pIsSymbol ')'

pBinOp :: String -> Parser Token T.Text (ASTExpr -> ASTExpr -> ASTExpr)
pBinOp op =     foldl1 (*>) (map pIsSymbol op)
            $>
                (\e1 e2 -> Op2Expr (EntityLoc (getStartLoc e1) (getEndLoc e2)) e1 (getOperator op) e2)
    where
        getOperator "+" = Plus
        getOperator "-" = Minus
        getOperator "*" = Mul
        getOperator "/" = Div
        getOperator "%" = Mod
        getOperator "^" = Pow
        getOperator ":" = Cons
        getOperator "==" = Equal
        getOperator "<" = Less
        getOperator ">" = Greater
        getOperator "<=" = LessEq
        getOperator ">=" = GreaterEq
        getOperator "!=" = Nequal
        getOperator "&&" = LogAnd
        getOperator "||" = LogOr
        getOperator _ = error "Binary operator not defined"

pUnaryOp :: String -> Parser Token T.Text (ASTExpr -> ASTExpr)
pUnaryOp "!" = pIsSymbol '!' $> (\e1 -> OpExpr (EntityLoc (getStartLoc e1) (getEndLoc e1)) UnNeg e1)
pUnaryOp "-" = pIsSymbol '-' $> (\e1 -> OpExpr (EntityLoc (getStartLoc e1) (getEndLoc e1)) UnMinus e1)
pUnaryOp _ = error "Unary operator not defined"

pExpr :: Parser Token Text ASTExpr
pExpr = foldr ($) baseExpr
        [
          pChainl (pBinOp "||")
        , pChainl (pBinOp "&&")
        , pChainl (pBinOp "==" <<|> pBinOp "!=")
        , pChainl (pBinOp "<=" <<|> pBinOp ">=" <<|> pBinOp "<" <<|> pBinOp ">")
        , pChainr (pBinOp ":") 
        , pChainl (pBinOp "+" <<|> pBinOp "-")
        , pChainl (pBinOp "*" <<|> pBinOp "/" <<|> pBinOp "%")
        , pFieldSelect
        , pChainr1 (pUnaryOp "!")
        , pChainr1 (pUnaryOp "-")
        ]

    where
        baseExpr = pParens pExpr
                   <<|> pIntExpr
                   <<|> pBoolExpr
                   <<|> pFunCallExpr
                   <<|> pEmptyListExpr
                   <<|> pTupExpr
                   <<|> pCharExpr
                   <<|> pIdentifierExpr

pTupExpr :: Parser Token Text ASTExpr 
pTupExpr = (\fst snd -> TupExpr (EntityLoc (getStartLoc fst) (getEndLoc snd)) fst snd) <$>
                (pIsSymbol '(' *> pExpr <* pIsSymbol ',') <*> pExpr <* pIsSymbol ')'

pIdentifierExpr :: Parser Token Text ASTExpr
pIdentifierExpr = IdentifierExpr <$> pIdentifier

pIntExpr :: Parser Token Text ASTExpr
pIntExpr = (\token@(MkToken loc (IntToken i)) -> IntExpr (getLoc token) i) <$>
                satisfy (\case
                            MkToken _ (IntToken _) -> True
                            _ -> False)

pCharExpr :: Parser Token Text ASTExpr
pCharExpr = (\token@(MkToken loc (CharToken c)) -> CharExpr (getLoc token) c) <$>
                satisfy (\case
                            MkToken _ (CharToken _) -> True
                            _ -> False)

pBoolExpr :: Parser Token Text ASTExpr
pBoolExpr = (\token@(MkToken loc (BoolToken b)) -> BoolExpr (getLoc token) b) <$>
                satisfy (\case
                            MkToken _ (BoolToken _) -> True
                            _ -> False)

pFunCallExpr :: Parser Token Text ASTExpr
pFunCallExpr = FunCallExpr <$> pFunCall

pFunCall :: Parser Token Text ASTFunCall
pFunCall = (\id@(ASTIdentifier loc1 _) args -> ASTFunCall loc1 id args)
                <$> pIdentifier
                <*> (pIsSymbol '(' *> pList pExpr (pIsSymbol ',') <* pIsSymbol ')')

pFieldSelect :: Parser Token Text ASTExpr -> Parser Token T.Text ASTExpr
pFieldSelect = pChainl2 (pIsSymbol '.' $> mkFunCallExpr) pIdentifier
    where
        mkFunCallExpr expr id@(ASTIdentifier loc1 _) = FunCallExpr $ ASTFunCall loc1 id [expr]

pEmptyListExpr :: Parser Token Text ASTExpr
pEmptyListExpr = liftA2 (\t1 t2 -> EmptyListExpr (EntityLoc (getStartLoc t1) (_2 %~ (+1) $ getEndLoc t2))) 
                        (pIsSymbol '[') (pIsSymbol ']')

pIdentifier :: Parser Token T.Text ASTIdentifier
pIdentifier =
    (\t@(MkToken _ (IdentifierToken val)) -> ASTIdentifier (getLoc t) val) <$>
    satisfy (\case
                (MkToken _ (IdentifierToken _)) -> True
                _ -> False
    ) <<|> pError (\case
        (ParserState _ (s:_)) ->
            "Expected an identifier but instead got '" <> T.pack (show s) <> "'"
        (ParserState _ []) ->
            "Expected an identifier but instead got EOF"
    )

pIsSymbol :: Char -> Parser Token Text Token
pIsSymbol c =
    satisfy ( \case
                (MkToken _ (SymbolToken c2)) | c == c2 -> True
                _ -> False
    ) <<|> pError (\case
        (ParserState _ (s:_)) ->
            "Expected character '" <> T.singleton c <>
            "' but instead got '" <> T.pack (show s) <> "'"
        (ParserState _ []) ->
            "Expected character '" <> T.singleton c <> "' but instead got EOF"
    )


-- note that: (someParser $> a) == someParser *> pure a 
pArrow :: Parser Token Text ()
pArrow = pIsSymbol '-' *> pIsSymbol '>' $> ()
    <<|> pError (\case
        (ParserState _ (s:_)) ->
            "Expected '->' but instead got '" <> T.pack (show s) <> "'"
        (ParserState _ []) ->
            "Expected '->' but instead got EOF"
    )

pBasicType :: Parser Token Text ASTType
pBasicType =
    (\(MkToken _ (TypeToken t)) -> toASTType t) <$>
            satisfy (\case
                        (MkToken _ (TypeToken Lex.VoidType)) -> False
                        (MkToken _ (TypeToken _)) -> True
                        _ -> False)
    <<|> pError (\case
        (ParserState _ (s:_)) ->
            "Expected a basic type but instead got '" <> T.pack (show s) <> "'"
        (ParserState _ []) ->
            "Expected a basic type but instead got EOF"
    )


pVoidType :: Parser Token e ASTType
pVoidType =
    (\(MkToken _ (TypeToken t)) -> toASTType t) <$>
            satisfy (\case
                        (MkToken _ (TypeToken Lex.VoidType)) -> True
                        _ -> False)

pFargs :: Parser Token Text [ASTIdentifier]
pFargs = pList pIdentifier $ pIsSymbol ','

pType :: Parser Token Text ASTType
pType = pBasicType
        <<|> ((\(ASTIdentifier _ v) -> ASTVarType v) <$> pIdentifier)
        <<|> tupError (liftA2 ASTTupleType (pIsSymbol '(' *> pType) (pIsSymbol ',' *> pType <* pIsSymbol ')'))
        <<|> listError (ASTListType <$> (pIsSymbol '[' *> pType <* pIsSymbol ']'))
    where
        tupError = pWrapErrors (const "Unable to parse tuple type: ")
        listError = pWrapErrors (const "Unable to parse list type: ")

pFunType :: Parser Token Text ASTType
pFunType = ASTFunType <$>
             (pTwice (pIsSymbol ':') *> pFtype <* pArrow <++> (pure <$> pRetType))
    where
        pFtype :: Parser Token Text [ASTType]
        pFtype = concat . maybeToList <$> pMaybe (some pType)
        pRetType :: Parser Token Text ASTType
        pRetType = pType <<|> pVoidType

pStmt :: Parser Token Text ASTStmt 
pStmt = pIfElseStmt
        <<|> pWhileStmt
        <<|> pAssignStmt
        <<|> pFunCallStmt
        <<|> pReturnStmt 

pIfElseStmt :: Parser Token Text ASTStmt 
pIfElseStmt =
    (\cond ifDo elseDo -> IfElse (EntityLoc (getStartLoc cond) (getEndLoc cond)) cond ifDo elseDo) <$>
    (pIf *> pExpr) <*> pBody <*> (pElse *> pBody)
    where
        pIf = satisfy ( \case
                (MkToken _ (KeywordToken Lex.If)) -> True
                _ -> False)
        pElse = satisfy ( \case
                (MkToken _ (KeywordToken Lex.Else)) -> True
                _ -> False)
        pBody = pIsSymbol '{' *> many' pStmt <* pIsSymbol '}'

pWhileStmt :: Parser Token Text ASTStmt 
pWhileStmt = 
    (\cond body -> While (EntityLoc (getStartLoc cond) (getEndLoc cond)) cond body) <$>
    (pWhile *> pExpr) <*> pBody
    where
        pWhile = satisfy ( \case
                (MkToken _ (KeywordToken Lex.While)) -> True
                _ -> False)
        pBody = pIsSymbol '{' *> many' pStmt <* pIsSymbol '}'

pAssignStmt :: Parser Token Text ASTStmt
pAssignStmt =
    (\id@(ASTIdentifier loc _) val -> Assign loc id val) <$>
    pIdentifier <* pIsSymbol '=' <*> pExpr <* pIsSymbol ';'

pFunCallStmt :: Parser Token Text ASTStmt 
pFunCallStmt = FunCallStmt <$> pFunCall <* pIsSymbol ';'

pReturnStmt :: Parser Token Text ASTStmt
pReturnStmt = pReturn *> (pReturnNoValue <<|> pReturnValue) 
    where
        pReturn = satisfy ( \case
                (MkToken _ (KeywordToken Lex.Return)) -> True
                _ -> False)
        pReturnNoValue = (\(MkToken (AlexPn _ l c) _) -> Return (EntityLoc (l,c) (l,c)) Nothing) <$> pIsSymbol ';' 
        pReturnValue = (\val (MkToken (AlexPn _ l c) _) -> Return (EntityLoc (l,c) (l,c)) Nothing) <$> pIdentifier <*> pIsSymbol ';' 
