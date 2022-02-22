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
pTupExpr = (\lParen fst snd rParen -> TupExpr (lParen |-| rParen) fst snd) <$>
                pIsSymbol '(' <*> pExpr <*> (pIsSymbol ',' *> pExpr) <*> pIsSymbol ')'

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
pFunCall = (\id args rParen -> ASTFunCall (id |-| rParen) id args)
                <$> pIdentifier
                <*> (pIsSymbol '(' *> pList pExpr (pIsSymbol ',')) <*> pIsSymbol ')'

pFieldSelect :: Parser Token Text ASTExpr -> Parser Token T.Text ASTExpr
pFieldSelect = pChainl2 (pIsSymbol '.' $> mkFunCallExpr) pIdentifier
    where
        mkFunCallExpr expr id = FunCallExpr $ ASTFunCall (expr |-| id) id [expr]

pEmptyListExpr :: Parser Token Text ASTExpr
pEmptyListExpr = liftA2 (\t1 t2 -> EmptyListExpr (t1 |-| t2))
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
    satisfy (\case
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
        satisfyAs (\case
                    t@(MkToken _ (TypeToken _)) -> toASTBasicType t
                    _ -> Nothing)
    <<|> pError (\case
        (ParserState _ (s:_)) ->
            "Expected a basic type but instead got '" <> T.pack (show s) <> "'"
        (ParserState _ []) ->
            "Expected a basic type but instead got EOF"
    )
    where
        toASTBasicType :: Token -> Maybe ASTType
        toASTBasicType t@(MkToken _ (TypeToken Lex.IntType)) = Just . ASTIntType $ getLoc t
        toASTBasicType t@(MkToken _ (TypeToken Lex.BoolType)) = Just . ASTBoolType $ getLoc t
        toASTBasicType t@(MkToken _ (TypeToken Lex.CharType)) = Just . ASTCharType $ getLoc t
        toASTBasicType _ = Nothing

pVoidType :: Parser Token e ASTType
pVoidType =
        satisfyAs (\case
                    t@(MkToken _ (TypeToken Lex.VoidType)) -> Just $ ASTVoidType (getLoc t)
                    _ -> Nothing)

pFargs :: Parser Token Text [ASTIdentifier]
pFargs = pList pIdentifier $ pIsSymbol ','


pType :: Parser Token Text ASTType
pType = pBasicType
        <<|> ((\i@(ASTIdentifier _ v) -> ASTVarType (getLoc i) v) <$> pIdentifier)
        <<|> tupError ((\start t1 t2 end -> ASTTupleType (start |-| end) t1 t2) 
                            <$> pIsSymbol '('
                            <*> pType
                            <*> (pIsSymbol ',' *> pType)
                            <*> pIsSymbol ')')
        <<|> listError ((\start t end -> ASTListType (start |-| end) t) 
                            <$> pIsSymbol '[' 
                            <*> pType 
                            <*> pIsSymbol ']')
    where
        tupError = pWrapErrors (const "Unable to parse tuple type: ")
        listError = pWrapErrors (const "Unable to parse list type: ")

pFunType :: Parser Token Text ASTType
pFunType = (\t r -> ASTFunType (t |-| r) (t ++ [r])) 
                <$> (pTwice (pIsSymbol ':') *> pFtype <* pArrow)
                <*> pRetType
            <<|> ((\t -> let start = getStartLoc t in ASTUnknownType (EntityLoc start start)) <$> peek)
    where
        pFtype :: Parser Token Text [ASTType]
        pFtype = concat . maybeToList <$> pMaybe (some pType)
        pRetType :: Parser Token Text ASTType
        pRetType = pType <<|> pVoidType

pAST :: Parser Token Text AST
pAST = AST <$> many' pASTLeaf
    where
        pASTLeaf = (ASTVar <$> pVarDecl) <<|> (ASTFun <$> pFunDecl)

pFunDecl :: Parser Token Text ASTFunDecl
pFunDecl = (\i fargs t body -> ASTFunDecl (i |-| body) i fargs t body)
                <$> pIdentifier 
                <*> (pIsSymbol '(' *> pFargs <* pIsSymbol ')')
                <*> pFunType
                <*> pFunBody

    where
        pFunBody = (\start v s end -> ASTFunBody (start |-| end) v s)
                        <$> pIsSymbol '{' 
                        <*> many' pVarDecl 
                        <*> many' pStmt
                        <*> pIsSymbol '}'

pVarDecl :: Parser Token Text ASTVarDecl
pVarDecl = (\t id expr end -> ASTVarDecl (t |-| end) t id expr) 
             <$> (pIsVar <<|> pType)
             <*> pIdentifier
             <*> pExpr
             <*> pIsSymbol ';'
    where
        pIsVar = ASTUnknownType . getLoc <$>
                    satisfy (\case (MkToken _ (KeywordToken Lex.Var)) -> True; _ -> False)

pStmt :: Parser Token Text ASTStmt
pStmt = pIfElseStmt
        <<|> pWhileStmt
        <<|> pAssignStmt
        <<|> pFunCallStmt
        <<|> pReturnStmt

pIfElseStmt :: Parser Token Text ASTStmt
pIfElseStmt =
    (\kIf cond ifDo elseDo rParen-> IfElseStmt (kIf |-| rParen) cond ifDo elseDo) <$>
    pIf <*> pExpr <* pIsSymbol '{' <*> pBody <* pIsSymbol '}' <*> (pElse *> pIsSymbol '{' *> pBody) <*> pIsSymbol '}'
    where
        pIf = satisfy ( \case
                (MkToken _ (KeywordToken Lex.If)) -> True
                _ -> False)
        pElse = satisfy ( \case
                (MkToken _ (KeywordToken Lex.Else)) -> True
                _ -> False)
        pBody = many' pStmt

pWhileStmt :: Parser Token Text ASTStmt 
pWhileStmt = 
    (\kWhile cond body rParen -> WhileStmt (kWhile |-| rParen) cond body) <$>
    pWhile <*> pExpr <* pIsSymbol '{' <*> pBody <*> pIsSymbol '}'
    where
        pWhile = satisfy ( \case
                (MkToken _ (KeywordToken Lex.While)) -> True
                _ -> False)
        pBody = many' pStmt

pAssignStmt :: Parser Token Text ASTStmt
pAssignStmt =
    (\id val semic -> AssignStmt (id |-| semic) id val) <$>
    pIdentifier <* pIsSymbol '=' <*> pExpr <*> pIsSymbol ';'

pFunCallStmt :: Parser Token Text ASTStmt 
pFunCallStmt = (\funCall semic -> FunCallStmt (funCall |-| semic) funCall) <$> pFunCall <*> pIsSymbol ';'

pReturnStmt :: Parser Token Text ASTStmt
pReturnStmt = pReturnNoValue <<|> pReturnValue
    where
        pReturn = satisfy ( \case
                (MkToken _ (KeywordToken Lex.Return)) -> True
                _ -> False)
        pReturnNoValue = (\kReturn semic -> ReturnStmt (kReturn |-| semic) Nothing) <$> pReturn <*> pIsSymbol ';' 
        pReturnValue = (\kReturn val semic -> ReturnStmt (kReturn |-| semic) (Just val)) <$> pReturn <*> pExpr <*> pIsSymbol ';' 

