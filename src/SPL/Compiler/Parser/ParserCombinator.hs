{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.Parser.ParserCombinator where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), Keyword(..), Type(..), AlexPosn(..))
import SPL.Compiler.Parser.AST
import Control.Applicative
import Control.Lens ((%~), _1, _2, _Left, _Right, traversed, folded, maximumOf)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Functor (($>))
import Data.Function ((&))
import Data.Either (isRight, isLeft, rights, lefts)
import Data.Maybe (maybeToList, listToMaybe)
import Data.Char (isSymbol)

newtype Parser s e a = Parser { runParser :: ParserState s -> [Either (Error e) (a, ParserState s)] }

data ParserState s = ParserState {
    tokensParsed :: Int,
    remainingTokens :: [s]
} deriving (Eq, Show)

-- The Error data type holds the depth (how many tokens have been parsed)
-- at which the error occured together with the actual error of type e
data Error e = Error Int e

instance Eq (Error e) where
    (Error i e) == (Error i2 e2) = i == i2

instance Ord (Error e) where
    (Error i e) `compare` (Error i2 e2) = i `compare` i2

instance Show e => Show (Error e) where
    show (Error _ e) = show e

instance Functor (Parser s e) where
    fmap :: (a -> b) -> Parser s e a -> Parser s e b
    fmap ab p = Parser $ \s -> traversed._Right._1 %~ ab $ runParser p s

instance Applicative (Parser s e) where
    pure a = Parser $ \s -> [Right (a, s)]

    (<*>) :: Parser s e (a -> b) -> Parser s e a -> Parser s e b
    pab <*> pa = pab >>= (\ab -> ab <$> pa)

instance Monad (Parser s e) where
    return = pure

    -- The bind operator selectively chooses which errors to keep
    -- if the `pa` parser returns only errors then it will return all those errors
    -- otherwise it will select only the successfully parsed results from `pa` and
    -- propagate those to the `apb` function
    pa >>= apb =
        Parser $ \s ->
            let as = runParser pa s in
                if null (rights as) then
                    -- useless map needed for typechecking
                    map (\(Left e) -> Left e) as
                else
                    concat [ runParser (apb a) s' | (a, s') <- rights as ]

instance Alternative (Parser s e) where
    -- note the identity law:
    -- empty <|> fa = fa and fa <|> empty = fa
    empty = Parser $ const []
    pa1 <|> pa2 =
        Parser $ \s -> runParser pa1 s ++ runParser pa2 s

infixr 3 <:>
(<:>) :: (Applicative f) => f a -> f [a] -> f [a]
x <:> y = liftA2 (:) x y

infixr 2 <++>
(<++>) :: (Applicative f) => f [a] -> f [a] -> f [a]
x <++> y = liftA2 (++) x y

infixr 1 <<|>
(<<|>) :: Parser s e a -> Parser s e a -> Parser s e a
x <<|> y =
    Parser $ \s ->
        case runParser x s of
            [] -> runParser y s
            xs | not $ null (rights xs) -> xs
               | otherwise ->
                    case runParser y s of
                        [] -> xs
                        ys | not $ null (rights ys) -> ys
                           | otherwise -> getLongestError (xs ++ ys)
    where
        getLongestError zs = maybeToList $ Left <$> maximumOf (folded._Left) zs

satisfy :: (s -> Bool) -> Parser s e s
satisfy f =
    Parser $ \case
                (ParserState cnt (a:rest)) | f a -> [Right (a, ParserState (cnt + 1) rest) ]
                _ -> []

-- Alternative definitions of `some` and `many`
-- These use the <<|> (can be seen as XOR)
-- instead of <|> (can be seen as OR)

-- some': one to many 
-- this is the same as many' but with the additional
-- requirement that we can parse at least once successfully
some' :: Parser s e a -> Parser s e [a]
some' fa = (:) <$> fa <*> (some' fa <<|> pure [])

-- many': zero to many 
-- this can be seen as parse until failure
-- and return the parsed values right until we had a failure
many' :: Parser s e a -> Parser s e [a]
many' fa = some' fa <<|> pure []

pTwice :: Parser s e a -> Parser s e [a]
pTwice p = p <:> (pure <$> p)

pMaybe :: Parser s e a -> Parser s e (Maybe a)
pMaybe p = (Just <$> p) <<|> pure Nothing

pList :: Parser s e a -> Parser s e b -> Parser s e [a]
pList pElement pDelimiter = (many' (pElement <* pDelimiter) <++> (pure <$> pElement)) <<|> pure []

pError :: (ParserState s -> e) -> Parser s e a
pError err = Parser $ \s@(ParserState cnt _) -> [Left (Error cnt (err s))]

pWrapErrors :: Semigroup e => (ParserState s -> e) -> Parser s e a -> Parser s e a
pWrapErrors err p =
    Parser $ \s ->
        let xs = runParser p s in
            traversed . _Left %~ (\(Error i e) -> Error i $ err s <> e) $ xs


-- Parse sentences of the following format in a left associative way: 
-- p (`op` p)* => (p `op` (p `op` (p `op` p)))
pChainl :: Parser s e (a -> a -> a) -> Parser s e a -> Parser s e a
pChainl op p = foldl (&) <$> p <*> many (flip <$> op <*> p)

-- Parse sentences of the following format in a right associative way: 
-- p (`op` p)* => (((p `op` p) `op` p) `op` p)
pChainr :: Parser s e (a -> a -> a) -> Parser s e a -> Parser s e a
pChainr op p = (&) <$> p <*> (flip <$> op <*> pChainr op p) <<|> p

-------------------------------------------------------------------

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
        , pChainl (pBinOp "==" <|> pBinOp "!=")
        , pChainl (pBinOp "<=" <|> pBinOp ">=" <|> pBinOp "<" <|> pBinOp ">")
        , pChainl (pBinOp "+" <|> pBinOp "-")
        , pChainl (pBinOp "*" <|> pBinOp "/" <|> pBinOp "%")
        ]

    where
        baseExpr = pParens pExpr
                   <<|> pUnaryOp "-" <*> pExpr
                   <<|> pUnaryOp "!" <*> pExpr
                   <<|> pIntExpr
                   <<|> pBoolExpr
                   <<|> pFunCallExpr
                   <<|> pEmptyListExpr
                   <<|> pTupExpr
                   <<|> pCharExpr
                   <<|> pIdentifierExpr

pTupExpr :: Parser Token Text ASTExpr 
pTupExpr = (\fst snd -> TupExpr (EntityLoc (getStartLoc fst) (getEndLoc  snd)) fst snd) <$>
                (pIsSymbol '(' *> pExpr <* pIsSymbol ',') <*> (pExpr <* pIsSymbol ')')

pIdentifierExpr :: Parser Token Text ASTExpr
pIdentifierExpr = IdentifierExpr <$> pIdentifier 

pIntExpr :: Parser Token Text ASTExpr 
pIntExpr = (\token@(MkToken loc (IntToken i)) -> IntExpr (tokenToEntityLoc token) i) <$>
                satisfy (\case
                            MkToken _ (IntToken _) -> True
                            _ -> False)

pCharExpr :: Parser Token Text ASTExpr
pCharExpr = (\token@(MkToken loc (CharToken c)) -> CharExpr (tokenToEntityLoc token) c) <$>
                satisfy (\case
                            MkToken _ (CharToken _) -> True
                            _ -> False)

pBoolExpr :: Parser Token Text ASTExpr
pBoolExpr = (\token@(MkToken loc (BoolToken b)) -> BoolExpr (tokenToEntityLoc token) b) <$>
                satisfy (\case
                            MkToken _ (BoolToken _) -> True
                            _ -> False)

pFunCallExpr :: Parser Token Text ASTExpr 
pFunCallExpr = FunCallExpr <$> pFunCall

pFunCall :: Parser Token Text ASTFunCall 
pFunCall = (\id@(ASTIdentifier loc1 _) args -> ASTFunCall loc1 id args) 
                <$> pIdentifier 
                <*> (pIsSymbol '(' *> pList pExpr (pIsSymbol ',') <* pIsSymbol ')')

pEmptyListExpr :: Parser Token Text ASTExpr
pEmptyListExpr = liftA2 (\t1 t2 -> EmptyListExpr (EntityLoc (tokLoc t1) (_2 %~ (+1) $ tokLoc t2))) (pIsSymbol '[') (pIsSymbol ']')

pIdentifier :: Parser Token T.Text ASTIdentifier
pIdentifier =
    (\t@(MkToken _ (IdentifierToken val)) -> ASTIdentifier (tokenToEntityLoc t) val) <$> 
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
                        (MkToken _ (TypeToken VoidType)) -> False
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
                        (MkToken _ (TypeToken VoidType)) -> True
                        _ -> False)

pFargs :: Parser Token Text [ASTIdentifier]
pFargs = (many' (pIdentifier <* pIsSymbol ',') <++> (maybeToList <$> pMaybe pIdentifier))

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
