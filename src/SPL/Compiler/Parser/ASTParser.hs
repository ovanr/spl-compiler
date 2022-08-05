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
pAST = ASTUnordered <$> (many' pASTLeaf <* pEnd)
    where
        pASTLeaf = (Left <$> pVarDecl) <<|> (Right <$> pFunDecl)
        pEnd = pReplaceError (mkError "Expected end of file here") $
                    satisfy (\case EOF -> True; _ -> False)

pFunDecl :: SPLParser ASTFunDecl
pFunDecl = pWrapErrors (\_ -> (<>) ["Function declaration"]) $
    (\i fargs t body -> ASTFunDecl (i |-| body) i fargs t body)
                <$> pIdentifier
                <*> (pIsSymbol '(' *> pFargs <* pIsSymbol ')')
                <*> ((pDblColon *>  pFunType) <<|> pUnknownType)
                <*> pFunBody

    where
        pFunBody = (\start stmts end -> ASTFunBody (start |-| end) stmts)
                        <$> pIsSymbol '{'
                        <*> some' pStmt
                        <*> pIsSymbol '}'
        pDblColon = pTwice (pIsSymbol ':')

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

pUnknownType :: SPLParser ASTType
pUnknownType =
    peek <&>
    \t -> let start = getStartLoc t
           in ASTUnknownType (EntityLoc start start)

pType :: SPLParser ASTType
pType =
    pWrapErrors (\_ -> (<>) ["Type"]) $
        noArgFunType <<|> (toType <$> pBaseType <*> pMaybe _pFunType)

    where
        noArgFunType = pWrapErrors (\_ -> (<>) ["Function type"]) $
                        toNoArgFunType <$> (pArrow *> pBaseType)
        toNoArgFunType r = ASTFunType (getLoc r) [] r
        toType x Nothing = x
        toType x (Just (ASTFunType _ xs r)) = ASTFunType (x |-| r) (x:xs) r
        toType _ _ = error "impossible"

pBaseType :: SPLParser ASTType
pBaseType = 
    pWrapErrors (\_ -> (<>) ["Simple Type"]) $
        pParensOrTupType
                <<|> pBasicType
                <<|> pVarType
                <<|> pListType

pVarType :: SPLParser ASTType
pVarType = (\i@(ASTIdentifier _ v) -> ASTVarType (getLoc i) v) <$> pIdentifier

pFunType :: SPLParser ASTType
pFunType = _pFunType <<|> pParens pFunType

_pFunType :: SPLParser ASTType
_pFunType =
    pWrapErrors (\_ -> (<>) ["Function type"]) $
        (\as r -> let loc = if null as then getLoc r else head as |-| r
                  in ASTFunType loc as r)
            <$> many' pBaseType
            <*> (pArrow *> pBaseType)

pListType :: SPLParser ASTType
pListType =
    pWrapErrors (\_ -> (<>) ["List type"]) $
        (\start t end -> ASTListType (start |-| end) t)
            <$> pIsSymbol '['
            <*> pType
            <*> pIsSymbol ']'

pParensOrTupType :: SPLParser ASTType
pParensOrTupType =
    pWrapErrors (\_ -> (<>) ["Tuple type or Parenthesis"]) $
        toType
        <$> pIsSymbol '('
        <*> pType
        <*> pMaybe (pIsSymbol ',' *> pWrapErrors (\_ -> (<>) ["Tuple Type Constructor"]) pType)
        <*> (pIsSymbol ')' <<|> pErrorMax (mkError "Expected ')' here"))

    where
        toType lParens typ1 (Just typ2) rParens =
            ASTTupleType (lParens |-| rParens) typ1 typ2
        toType _ t Nothing rParens = t

-- note that: (someParser $> a) == someParser *> pure a 
pArrow :: SPLParser ()
pArrow = pIsSymbol '-' *> pIsSymbol '>' $> ()
    <<|> pError (mkError "Expected '->' here")

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
pStmt = pIfElseStmt
        <<|> pWhileStmt
        <<|> (VarDeclStmt <$> pVarDecl)
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
    (\kWhile cond body -> WhileStmt (kWhile |-| body) cond body)
        <$> pWhile
        <*> pExpr 
        <*> (pIsSymbol '{' *> pBody <* pIsSymbol '}' <<|> pure <$> pStmt)
    where
        pWhile = satisfy (\case
                            (MkToken _ (KeywordToken Lex.While)) -> True
                            _ -> False)
        pBody = many' pStmt

pField :: SPLParser Field
pField =
    pWrapErrors (\_ -> (<>) ["Field selector"]) $
        satisfyAs (\case
            t@(MkToken _ (IdentifierToken "hd")) -> Just . Hd . getLoc $ t
            t@(MkToken _ (IdentifierToken "tl")) -> Just . Tl . getLoc $ t
            t@(MkToken _ (IdentifierToken "fst")) -> Just . Fst . getLoc $ t
            t@(MkToken _ (IdentifierToken "snd")) -> Just . Snd . getLoc $ t
            _ -> Nothing
        )

pAssignStmt :: SPLParser ASTStmt
pAssignStmt =
    pWrapErrors (\_ -> (<>) ["Assignment statement"]) $
    (\id fds val semic -> AssignStmt (id |-| semic) id fds val)
        <$> pIdentifier
        <*> many' (pIsSymbol '.' *> pField) <* pIsSymbol '='
        <*> pExpr
        <*> pIsSymbol ';'

pFunCallStmt :: SPLParser ASTStmt
pFunCallStmt =
    pWrapErrors (\_ -> (<>) ["Function call statement"]) $
    (\call col -> FunCallStmt call)
        <$> pFunCall
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

pFunCall :: SPLParser ASTFunCall
pFunCall = literalFunCall <<|> bracketedFunCall
    where
        bracketedFunCall = 
            (\e args rParen -> ASTFunCall (e |-| rParen) e args)
                <$> pParens _pExpr
                <*> (pIsSymbol '(' *> pList _pExpr (pIsSymbol ','))
                <*> pIsSymbol ')'
        literalFunCall = 
            (\id args rParen -> ASTFunCall (id |-| rParen) (IdentifierExpr id) args)
                <$> pIdentifier
                <*> (pIsSymbol '(' *> pList _pExpr (pIsSymbol ','))
                <*> pIsSymbol ')'

pExpr :: SPLParser ASTExpr
pExpr = pWrapErrors (\_ -> (<>) ["Expression"]) _pExpr

_pExpr :: SPLParser ASTExpr
_pExpr =
    foldr ($) baseExpr
        [
          pChainl (pBinOp "||")
        , pChainl (pBinOp "&&")
        , pNonAssocOp (mkError "Unable to parse non-associative operator") (pBinOp "==" <<|> pBinOp "!=")
        , pNonAssocOp (mkError "Unable to parse non-associative operator") 
            (pBinOp "<=" <<|> pBinOp ">=" <<|> pBinOp "<" <<|> pBinOp ">")
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
                   <<|> pIdentifierExpr
                   <<|> pListExpr
                   <<|> pCharExpr
                   <<|> pStringExpr
                   <<|> pErrorMax (mkError "Unknown expression encountered here")

pFunOrFieldFollowUp :: SPLParser (ASTExpr -> ASTExpr)
pFunOrFieldFollowUp = (toExprGen <$> pAlternative pFunCall pFieldSelector) <<|> pure id
    where
        pFieldSelector = some' (pIsSymbol '.' *> pField)
        pFunCall = (,) <$> (pIsSymbol '(' *> pList _pExpr (pIsSymbol ',')) <*> pIsSymbol ')'

        toExprGen (Left (args, endC)) baseExpr =
            let loc = baseExpr |-| endC
            in FunCallExpr $ ASTFunCall loc baseExpr args
        toExprGen (Right []) baseExpr = error "impossible"
        toExprGen (Right (f:fs)) baseExpr =
            let loc = baseExpr |-| if null fs then f else last fs
            in FieldSelectExpr loc baseExpr (f:fs)

pIdentifierExpr :: SPLParser ASTExpr
pIdentifierExpr =
    toExpr <$> pIdentifier <*> pFunOrFieldFollowUp

    where
        toExpr id exprGen = exprGen (IdentifierExpr id)

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
    pWrapErrors (\_ -> (<>) ["Tuple constructor or Parenthesis or Function call"]) $
        toASTExpr
            <$> pIsSymbol '('
            <*> _pExpr
            <*> pMaybe (pIsSymbol ',' *> (pWrapErrors (\_ -> (<>) ["Tuple Constructor"]) _pExpr))
            <*> (pIsSymbol ')' <<|> pErrorMax (mkError "Expected ')' here"))
            <*> pFunOrFieldFollowUp

    where
        toASTExpr lParens expr1 (Just expr2) rParens exprGen =
            exprGen $ TupExpr (lParens |-| rParens) expr1 expr2
        toASTExpr _ expr Nothing rParens exprGen = exprGen expr

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
                                       (EmptyCharListExpr loc)
                                       (T.unpack str)
pBoolExpr :: SPLParser ASTExpr
pBoolExpr = (\token@(MkToken loc (BoolToken b)) -> BoolExpr (getLoc token) b) <$>
                satisfy (\case
                            MkToken _ (BoolToken _) -> True
                            _ -> False)

pListExpr :: SPLParser ASTExpr
pListExpr =
    toASTExpr <$> pIsSymbol '['
              <*> pList _pExpr (pIsSymbol ',')
              <*> pIsSymbol ']'
              <*> pFunOrFieldFollowUp
    where
        toASTExpr lParens [] rParens exprGen = exprGen $ EmptyListExpr (lParens |-| rParens)
        toASTExpr lParens exprs rParens exprGen =
            exprGen $ foldr (\e acc -> Op2Expr (getLoc e) e Cons acc) (EmptyListExpr $ getLoc rParens) exprs
