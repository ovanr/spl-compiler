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
import Data.Function ((&))
import Data.Either (isRight, isLeft, rights, lefts)
import Data.Maybe (maybeToList)

newtype Parser s e a = Parser {
    runParser :: ParserState s -> [Either (Error e) (a, ParserState s)]
}

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

    -- The <*> operator selectively chooses which errors to keep
    -- if the `pab` parser returns only errors then it will return all those errors
    -- otherwise it will select only the successfully parsed results from `pab` and
    -- propagate those to the `pa` parser
    (<*>) :: Parser s e (a -> b) -> Parser s e a -> Parser s e b
    pab <*> pa =
        Parser $ \s ->
            let abs = runParser pab s in
                if null (rights abs) then
                    -- useless map needed for typechecking
                    map (\(Left e) -> Left e) abs
                else
                    concat [ runParser (ab <$> pa) s' | (ab, s') <- rights abs ]

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
pChainl op p = foldl (&) <$> p <*> many' (flip <$> op <*> p)

-- Parse sentences of the following format in a left associative way: 
-- p (`op` p)* => (p `op` (p `op` (p `op` p)))
pChainl2 :: Parser s e (a -> b -> a) -> Parser s e b -> Parser s e a -> Parser s e a
pChainl2 op pc p = foldl (&) <$> p <*> many' (flip <$> op <*> pc)

-- Parse sentences of the following format in a right associative way: 
-- p (`op` p)* => (((p `op` p) `op` p) `op` p)
pChainr :: Parser s e (a -> a -> a) -> Parser s e a -> Parser s e a
pChainr op p = (&) <$> p <*> (flip <$> op <*> pChainr op p) <<|> p

-- Parse sentences of the following format in a right associative way: 
-- op* p => op (op (op p))
pChainr1 :: Parser s e (a -> a) -> Parser s e a -> Parser s e a
pChainr1 op p = (op <*> pChainr1 op p) <<|> p

