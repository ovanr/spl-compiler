{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module SPL.Compiler.Parser.ASTParser where

import Control.Applicative
import Control.Lens ((%~), _1, _2, (^?), ix)
import qualified Data.Text as T
import Data.Text (Text)
import Data.Functor (($>), (<&>))
import Data.Function ((&))
import Data.Foldable
import Control.Monad.State
import Data.Maybe (maybeToList)

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..))
import qualified SPL.Compiler.Lexer.AlexLexGen as Lex (Keyword(..), Type(..))
import SPL.Compiler.Parser.ParserCombinator
import SPL.Compiler.Parser.AST
import SPL.Compiler.Parser.ASTEntityLocation
import SPL.Compiler.Common.EntityLocation
import SPL.Compiler.Common.Error

type SPLParser a = Parser Token [Text] a

pParens :: SPLParser a -> SPLParser a
pParens p =
    pIsSymbol '('
    *> p <* (pIsSymbol ')' <<|> pError (mkError "Expected closed bracket ')' here "))

pIsSymbol :: Char -> SPLParser Token
pIsSymbol c =
    satisfy (\case
               (MkToken _ (SymbolToken c2)) | c == c2 -> True
               _ -> False
    ) <<|> pError (mkError $ "Expected character '" <> T.singleton c <> "' here")

pIdentifier :: SPLParser ASTIdentifier
pIdentifier =
    (\t@(MkToken _ (IdentifierToken val)) -> ASTIdentifier (getLoc t) val) <$>
    satisfy (\case
               (MkToken _ (IdentifierToken _)) -> True
               _ -> False
    ) <<|> pError (mkError "Expected identifier here")

mkError :: Text -> ParserState Token -> [Text]
mkError err state@(ParserState _ (s@(MkToken _ t):_) _ _) =
        evalState (definition err s) state
mkError err ParserState{} = [err]

pAST :: SPLParser AST
pAST = AST <$> (many' pASTLeaf <* pEnd)
    where
        pASTLeaf = (ASTVar <$> pVarDecl) <<|> (ASTFun <$> pFunDecl)
        pEnd = pReplaceError (mkError "Expected end of file here") $
                    satisfy (\case EOF -> True; _ -> False)

pFunDecl :: SPLParser ASTFunDecl
pFunDecl = pWrapErrors (\_ -> (<>) ["Function declaration"]) $
    (\i fargs t body -> ASTFunDecl (i |-| body) i fargs t body)
                <$> pIdentifier
                <*> (pIsSymbol '(' *> pFargs <* pIsSymbol ')')
                <*> pFunType
                <*> pFunBody

    where
        pFunBody = (\start v s end -> ASTFunBody (start |-| end) v s)
                        <$> pIsSymbol '{'
                        <*> many' pVarDecl
                        <*> some' pStmt
                        <*> pIsSymbol '}'

pFargs :: SPLParser [ASTIdentifier]
pFargs = pList pIdentifier $ pIsSymbol ','

pBasicType :: SPLParser ASTType
pBasicType =
        satisfyAs (\case
                     t@(MkToken _ (TypeToken _)) -> toASTBasicType t
                     _ -> Nothing)
    <<|> pError (mkError "Expected basic type here")

    where
        toASTBasicType :: Token -> Maybe ASTType
        toASTBasicType t@(MkToken _ (TypeToken Lex.IntType)) =
            Just . ASTIntType $ getLoc t
        toASTBasicType t@(MkToken _ (TypeToken Lex.BoolType)) =
            Just . ASTBoolType $ getLoc t
        toASTBasicType t@(MkToken _ (TypeToken Lex.CharType)) =
            Just . ASTCharType $ getLoc t
        toASTBasicType t@(MkToken _ (TypeToken Lex.VoidType)) =
            Just . ASTVoidType $ getLoc t
        toASTBasicType _ = Nothing

pType :: SPLParser ASTType
pType =
    pWrapErrors (\_ -> (<>) ["Type"]) $
        pBasicType
        <<|> (identifierToVar <$> pIdentifier)
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
        identifierToVar i@(ASTIdentifier _ v) = ASTVarType (getLoc i) v
        tupError = pWrapErrors (\_ -> (<>) ["Tuple type"])
        listError = pWrapErrors (\_ -> (<>) ["List type"])

-- note that: (someParser $> a) == someParser *> pure a 
pArrow :: SPLParser ()
pArrow = pIsSymbol '-' *> pIsSymbol '>' $> ()
    <<|> pError (mkError "Expected '->' here")

pFunType :: SPLParser ASTType
pFunType =
    pWrapErrors (\_ -> (<>) ["Function type"]) $
            (\t r -> ASTFunType (t |-| r) (t ++ [r]))
                <$> (pTwice (pIsSymbol ':') *> pFtype <* pArrow)
                <*> pRetType
            <<|> pUnknownType
    where
        pUnknownType =
            peek <&>
            \t -> let start = getStartLoc t
                   in ASTUnknownType (EntityLoc start start)
        pFtype :: SPLParser [ASTType]
        pFtype = many' pType
        pRetType :: SPLParser ASTType
        pRetType = pType

pVarDecl :: SPLParser ASTVarDecl
pVarDecl =
    pWrapErrors (\_ -> (<>) ["Variable declaration"]) $
        (\t id expr end -> ASTVarDecl (t |-| end) t id expr)
                 <$> (pIsVar <<|> pType)
                 <*> pIdentifier <* pIsSymbol '='
                 <*> pExpr
                 <*> pIsSymbol ';'
    where
        pIsVar = ASTUnknownType . getLoc <$>
                    satisfy (\case
                               (MkToken _ (KeywordToken Lex.Var)) -> True
                               _ -> False)

pStmt :: SPLParser ASTStmt
pStmt =
        pIfElseStmt
        <<|> pWhileStmt
        <<|> pAssignStmt
        <<|> pFunCallStmt
        <<|> pReturnStmt

infixr 5 <*|
(<*|) :: Locatable b => Parser Token e a -> Parser Token e b -> Parser Token e (a, EntityLoc)
(<*|) = liftA2 (\p t -> (p, getLoc t))

pIfElseStmt :: SPLParser ASTStmt
pIfElseStmt =
    pWrapErrors (\_ -> (<>) ["If statement"]) $
        toASTStmt
        <$> pIf
        <*> (pIsSymbol '(' *> pExpr <* pIsSymbol ')')
        <*> pBody
        <*> pMaybe (pElse *> pBody)
    where
        toASTStmt kIf cond (ifDo, _) (Just (elseDo, elseEnd)) = IfElseStmt (kIf |-| elseEnd) cond ifDo elseDo
        toASTStmt kIf cond (ifDo, ifEnd) Nothing = IfElseStmt (kIf |-| ifEnd) cond ifDo []
        pIf = satisfy (\case
                         (MkToken _ (KeywordToken Lex.If)) -> True
                         _ -> False)
        pElse = satisfy (\case
                           (MkToken _ (KeywordToken Lex.Else)) -> True
                           _ -> False)
        pBody = (pIsSymbol '{' *> many' pStmt <*| pIsSymbol '}') <<|> ((\s -> ([s], getLoc s)) <$> pStmt)

pWhileStmt :: SPLParser ASTStmt
pWhileStmt =
    pWrapErrors (\_ -> (<>) ["While statement"]) $
    (\kWhile cond body rParen -> WhileStmt (kWhile |-| rParen) cond body)
        <$> pWhile
        <*> pExpr <* pIsSymbol '{'
        <*> pBody
        <*> pIsSymbol '}'
    where
        pWhile = satisfy (\case
                            (MkToken _ (KeywordToken Lex.While)) -> True
                            _ -> False)
        pBody = many' pStmt

pAssignStmt :: SPLParser ASTStmt
pAssignStmt =
    pWrapErrors (\_ -> (<>) ["Assignment statement"]) $
    (\id val semic -> AssignStmt (id |-| semic) id val)
        <$> pFieldSelect  <* pIsSymbol '='
        <*> pExpr
        <*> pIsSymbol ';'

pFunCallStmt :: SPLParser ASTStmt
pFunCallStmt =
    pWrapErrors (\_ -> (<>) ["Function call statement"]) $
    (\call col -> FunCallStmt (call |-| col) call)
        <$> pFunCall False
        <*> pIsSymbol ';'

pReturnStmt :: SPLParser ASTStmt
pReturnStmt =
    pWrapErrors (\_ -> (<>) ["Return statement"]) $
        pReturnNoValue <<|> pReturnValue
    where
        pReturn = satisfy (\case
                             (MkToken _ (KeywordToken Lex.Return)) -> True
                             _ -> False)
        pReturnNoValue =
            (\ret col -> ReturnStmt (ret |-| col) Nothing)
                <$> pReturn
                <*> pIsSymbol ';'
        pReturnValue =
            (\ret val col -> ReturnStmt (ret |-| col) (Just val))
                <$> pReturn
                <*> pExpr
                <*> pIsSymbol ';'

pFunCall :: Bool -> SPLParser ASTFunCall
pFunCall fromExprCxt = (\id args rParen -> ASTFunCall (id |-| rParen) id args)
                <$> pIdentifier
                <*> (pIsSymbol '(' *> pList (if fromExprCxt then _pExpr else pExpr) (pIsSymbol ','))
                <*> pIsSymbol ')'

pExpr :: SPLParser ASTExpr
pExpr = pWrapErrors (\_ -> (<>) ["Expression"]) _pExpr

_pExpr :: SPLParser ASTExpr
_pExpr =
    foldr ($) baseExpr
        [
          pChainl (pBinOp "||")
        , pChainl (pBinOp "&&")
        , pChainl (pBinOp "==" <<|> pBinOp "!=")
        , pChainl (pBinOp "<=" <<|> pBinOp ">=" <<|> pBinOp "<" <<|> pBinOp ">")
        , pChainr (pBinOp ":")
        , pChainl (pBinOp "+" <<|> pBinOp "-")
        , pChainl (pBinOp "*" <<|> pBinOp "/" <<|> pBinOp "^" <<|> pBinOp "%")
        , pChainr1 (pUnaryOp "!")
        , pChainr1 (pUnaryOp "-")
        ]

    where
        baseExpr = pTupExprOrParens
                   <<|> pIntExpr
                   <<|> pBoolExpr
                   <<|> pFunCallExpr
                   <<|> pEmptyListExpr
                   <<|> pCharExpr
                   <<|> pStringExpr
                   <<|> pFieldSelectExpr
                   <<|> pError (mkError "Unknown expression encountered here")

pUnaryOp :: String -> SPLParser (ASTExpr -> ASTExpr)
pUnaryOp "!" = pReplaceError (mkError "Expected unary operator '!' here") (pIsSymbol '!')
                    $> (\e1 -> OpExpr (e1 |-| e1) UnNeg e1)
pUnaryOp "-" = pReplaceError (mkError "Expected unary operator '-' here") (pIsSymbol '-')
                    $> (\e1 -> OpExpr (e1 |-| e1) UnMinus e1)
pUnaryOp _ = error "Unary operator not defined"

pBinOp :: String -> SPLParser (ASTExpr -> ASTExpr -> ASTExpr)
pBinOp op = pReplaceError
                (mkError $ "Expected binary operator " <> T.pack (show op) <> " here")
                (foldl1 (*>) (map pIsSymbol op))
            $> (\e1 e2 -> Op2Expr (e1 |-| e2) e1 (getOperator op) e2)
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

pTupExprOrParens :: SPLParser ASTExpr
pTupExprOrParens =
    pWrapErrors (\_ -> (<>) ["Tuple constructor or Parens"]) $
        toASTExpr
            <$> pIsSymbol '('
            <*> _pExpr
            <*> pMaybe (pIsSymbol ',' *> (pWrapErrors (\_ -> (<>) ["Tuple Constructor"]) _pExpr))
            <*> pIsSymbol ')'

    where
        toASTExpr lParens expr1 (Just expr2) rParens = TupExpr (lParens |-| rParens) expr1 expr2
        toASTExpr _ expr Nothing _ = expr

pFieldSelectExpr :: SPLParser ASTExpr
pFieldSelectExpr = FieldSelectExpr <$> pFieldSelect

pIntExpr :: SPLParser ASTExpr
pIntExpr = (\token@(MkToken loc (IntToken i)) -> IntExpr (getLoc token) i) <$>
                satisfy (\case
                            MkToken _ (IntToken _) -> True
                            _ -> False)

pCharExpr :: SPLParser ASTExpr
pCharExpr = (\token@(MkToken loc (CharToken c)) -> CharExpr (getLoc token) c) <$>
                satisfy (\case
                            MkToken _ (CharToken _) -> True
                            _ -> False)

pStringExpr :: SPLParser ASTExpr
pStringExpr = satisfyAs (\case
                            t@(MkToken _ (StringToken str)) -> Just $ toConsCharExpr (getLoc t) str
                            _ -> Nothing)
    where
        toConsCharExpr loc str = foldr (\c acc -> Op2Expr loc (CharExpr loc c) Cons acc) 
                                       (EmptyListExpr loc) 
                                       (T.unpack str)
pBoolExpr :: SPLParser ASTExpr
pBoolExpr = (\token@(MkToken loc (BoolToken b)) -> BoolExpr (getLoc token) b) <$>
                satisfy (\case
                            MkToken _ (BoolToken _) -> True
                            _ -> False)

pFunCallExpr :: SPLParser ASTExpr
pFunCallExpr = FunCallExpr <$> pFunCall True

pFieldSelect :: SPLParser ASTFieldSelector
pFieldSelect =
    pWrapErrors (\_ -> (<>) ["Field selector"]) $
        liftA2 mkFieldSelector pIdentifier (many' (pIsSymbol '.' *> pField))
    where
        pField =
            satisfyAs (\case
                t@(MkToken _ (IdentifierToken "hd")) -> Just . Hd . getLoc $ t
                t@(MkToken _ (IdentifierToken "tl")) -> Just . Tl . getLoc $ t
                t@(MkToken _ (IdentifierToken "fst")) -> Just . Fst . getLoc $ t
                t@(MkToken _ (IdentifierToken "snd")) -> Just . Snd . getLoc $ t
                _ -> Nothing
            )

        mkFieldSelector id [] = ASTFieldSelector (id |-| id) id []
        mkFieldSelector id fs = ASTFieldSelector (id |-| last fs) id fs

pEmptyListExpr :: SPLParser ASTExpr
pEmptyListExpr = liftA2 (\t1 t2 -> EmptyListExpr (t1 |-| t2))
                            (pIsSymbol '[') (pIsSymbol ']')
