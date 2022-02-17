{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module SPL.Compiler.Parser.ParserCombinator where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), Keyword(..), Type(..), AlexPosn(..))
import SPL.Compiler.Parser.AST (ASTType(..), ASTExpr(..), toASTType, EntityLoc(..), ASTFunCall(..), ASTIdentifier(..))
import Control.Applicative
import Control.Lens ((%~), _1, _Left, _Right, traversed, folded, maximumOf)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Functor (($>))
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

pIdentifier :: Parser Token T.Text Token
pIdentifier =
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

pTwice :: Parser s e a -> Parser s e [a]
pTwice p = p <:> (pure <$> p)

pMaybe :: Parser s e a -> Parser s e (Maybe a)
pMaybe p = (Just <$> p) <<|> pure Nothing

pError :: (ParserState s -> e) -> Parser s e a
pError err = Parser $ \s@(ParserState cnt _) -> [Left (Error cnt (err s))]

pWrapErrors :: Semigroup e => (ParserState s -> e) -> Parser s e a -> Parser s e a
pWrapErrors err p = 
    Parser $ \s -> 
        let xs = runParser p s in 
            traversed . _Left %~ (\(Error i e) -> Error i $ err s <> e) $ xs 

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

pFargs :: Parser Token Text [Token]
pFargs = many' (pIdentifier <* pIsSymbol ',') <++> (pure <$> pIdentifier)

pType :: Parser Token Text ASTType
pType = pBasicType
        <<|> ((\(MkToken _ (IdentifierToken v)) -> ASTVarType v) <$> pIdentifier)
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

alexPosnToEntityLoc :: Token -> EntityLoc
alexPosnToEntityLoc token@(MkToken (AlexPn t l c) splToken) = EntityLoc (l,c) (l,c + lengthOfToken token)
    where
        lengthOfToken :: Token -> Int -- Add proper implementation later
        lengthOfToken token = 0
alexPosnToEntityLoc _ = EntityLoc (0,0) (0,0)

pInt :: Parser Token Text ASTExpr 
pInt = (\token@(MkToken loc (IntToken i)) -> IntExpr (alexPosnToEntityLoc token) i) <$>
                satisfy (\case
                            MkToken _ (IntToken _) -> True
                            _ -> False)

pChar :: Parser Token Text ASTExpr
pChar = (\token@(MkToken loc (CharToken c)) -> CharExpr (alexPosnToEntityLoc token) c) <$>
                satisfy (\case
                            MkToken _ (CharToken _) -> True
                            _ -> False)

pBool :: Parser Token Text ASTExpr
pBool = (\token@(MkToken loc (BoolToken b)) -> BoolExpr (alexPosnToEntityLoc token) b) <$>
                satisfy (\case
                            MkToken _ (BoolToken _) -> True
                            _ -> False)

pFunCallExpr :: Parser Token Text ASTExpr 
pFunCallExpr = FunCallExpr <$> pFunCall

locationRange :: EntityLoc -> EntityLoc -> EntityLoc 
locationRange (EntityLoc start _) (EntityLoc _ end) = EntityLoc start end

pFunCall :: Parser Token Text ASTFunCall 
pFunCall = (\id@(ASTIdentifier loc1 _) args -> ASTFunCall loc1 id args) <$> pIdentifier <*> (isSymbol '(' *> pList pExpr (isSymbol ',') <* isSymbol ')')


pList :: Parser s e a -> Parser s e a -> Parser s e [a]
pList pElement pDelimiter = (many' (pElement <* pDelimiter) <++> (pure <$> pElement)) <<|> pure []


pExpr :: Parser Token Text ASTExpr 
pExpr = undefined
