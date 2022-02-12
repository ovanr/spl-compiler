{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module SPL.Compiler.Parser.ParserCombinator where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), Keyword(..), Type(..))
import SPL.Compiler.Parser.AST (ASTType(..), toASTType)
import Data.Functor (($>))
import qualified Data.Text as T
import Control.Applicative
import Data.Maybe (maybeToList)

newtype Parser s a = Parser { runParser :: [s] -> [(a, [s])] }

instance Functor (Parser s) where
    fmap :: (a -> b) -> Parser s a -> Parser s b
    fmap ab p = Parser $ \s -> [ (ab a, s') | (a, s') <- runParser p s ]

instance Applicative (Parser s) where
    pure a = Parser $ \s -> [(a, s)]
    (<*>) :: Parser s (a -> b) -> Parser s a -> Parser s b
    pab <*> pa =
        Parser $ \s -> [ (ab a, s'') | (ab, s') <- runParser pab s, (a, s'') <- runParser pa s' ]

instance Monad (Parser s) where
    return = pure
    pa >>= apb =
        Parser $ \s -> concat [ runParser (apb a) s' | (a, s') <- runParser pa s ]

instance Alternative (Parser s) where
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
(<<|>) :: Parser s a -> Parser s a -> Parser s a
x <<|> y =
    Parser $ \s ->
        case runParser x s of
            [] -> runParser y s
            result -> result

satisfy :: (s -> Bool) -> Parser s s
satisfy f =
    Parser $ \case
                (a:rest) | f a -> [(a, rest)]
                _ -> []

-- Alternative definitions of `some` and `many`
-- These use the <<|> (can be seen as XOR)
-- instead of <|> (can be seen as OR)

-- some': one to many 
-- this is the same as many' but with the additional
-- requirement that we can parse at least once successfully
some' :: Parser s a -> Parser s [a]
some' fa = (:) <$> fa <*> (some' fa <<|> pure [])

-- many': zero to many 
-- this can be seen as parse until failure
-- and return the parsed values right until we had a failure
many' :: Parser s a -> Parser s [a]
many' fa = some' fa <<|> pure []

pIdentifier :: Parser Token Token
pIdentifier =
    satisfy $ \case
                (IdentifierToken _) -> True
                _ -> False

pIsSymbol :: Char -> Parser Token Token
pIsSymbol c =
    satisfy $ \case
                (SymbolToken c2) | c == c2 -> True
                _ -> False

pTwice :: Parser s a -> Parser s [a]
pTwice p = p <:> (pure <$> p)

pMaybe :: Parser s a -> Parser s (Maybe a)
pMaybe p = (Just <$> p) <<|> pure Nothing

-- note that: (someParser $> a) == someParser *> pure a 
pArrow :: Parser Token ()
pArrow = pIsSymbol '-' *> pIsSymbol '>' $> ()

pBasicType :: Parser Token ASTType
pBasicType =
    (\(TypeToken t) -> toASTType t) <$>
            satisfy (\case
                        (TypeToken VoidType) -> False
                        (TypeToken _) -> True
                        _ -> False)

pVoidType :: Parser Token ASTType
pVoidType =
    (\(TypeToken t) -> toASTType t) <$>
            satisfy (\case
                        (TypeToken VoidType) -> True
                        _ -> False)

pFargs :: Parser Token [Token]
pFargs = many' (pIdentifier <* pIsSymbol ',') <++> (pure <$> pIdentifier)

pType :: Parser Token ASTType
pType = pBasicType
        <<|> ((\(IdentifierToken v) -> ASTVarType v) <$> pIdentifier)
        <<|> liftA2 ASTTupleType (pIsSymbol '(' *> pType) (pIsSymbol ',' *> pType <* pIsSymbol ')')
        <<|> ASTListType <$> (pIsSymbol '[' *> pType <* pIsSymbol ']')

pFunType :: Parser Token ASTType
pFunType = ASTFunType <$>
             (pTwice (pIsSymbol ':') *> pFtype <* pArrow <++> (pure <$> pRetType))
    where
        pFtype :: Parser Token [ASTType]
        pFtype = concat . maybeToList <$> pMaybe (some pType)
        pRetType :: Parser Token ASTType
        pRetType = pType <<|> pVoidType
