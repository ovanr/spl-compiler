{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module SPL.Compiler.Parser.ParserCombinator where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), Keyword(..), Type(..), AlexPosn(..))
import SPL.Compiler.Parser.AST
import SPL.Compiler.Common.Error hiding (Error)

import Control.Applicative
import Control.Lens ((%~), _1, _2, _Left, _Right, _Just, traversed, folded, maximumOf)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Function ((&))
import Data.Foldable
import Data.Either (isRight, isLeft, rights, lefts)
import Data.Maybe (maybeToList, isJust, fromJust)

newtype Parser s e a = Parser {
    runParser :: Monoid e => ParserState s -> (Maybe (a, ParserState s), Maybe (Error e))
}

data ParserState s = ParserState {
    tokensParsed :: Int,
    remainingTokens :: [s],
    sourcePath :: FilePath,
    sourceCode :: [Text]
} deriving (Eq, Show)

instance ContainsSource (ParserState s) where
    getFilePath = sourcePath
    getSource = sourceCode

-- The Error data type holds the depth (how many tokens have been parsed)
-- at which the error occured together with the actual error of type e
data Error e = Error {
    depth :: Int,
    errMsg :: e
}

instance Eq (Error e) where
    (Error i e) == (Error i2 e2) = i == i2

instance Ord (Error e) where
    (Error i e) `compare` (Error i2 e2) = i `compare` i2

instance Show e => Show (Error e) where
    show (Error _ e) = show e

instance Semigroup e => Semigroup (Error e) where
    err1@(Error d1 _) <> err2@(Error d2 _) = 
        if d1 > d2 then 
            err1
        else 
            err2

instance Monoid e => Monoid (Error e) where
    mempty = Error 0 mempty
    mappend = (<>)

instance Functor (Parser s e) where
    fmap :: (a -> b) -> Parser s e a -> Parser s e b
    fmap ab p = Parser $ \s -> runParser p s & _1._Just._1 %~ ab 

instance Applicative (Parser s e) where
    pure a = Parser $ \s -> (Just (a, s), Nothing)

    -- The <*> operator selectively chooses which errors to keep
    -- if the `pab` parser returns only errors then it will return all those errors
    -- otherwise it will select only the successfully parsed results from `pab` and
    -- propagate those to the `pa` parser
    (<*>) :: Parser s e (a -> b) -> Parser s e a -> Parser s e b
    pab <*> pa =
        Parser $ \s ->
            let abs = runParser pab s in
            case abs of
                (Nothing, err) -> (Nothing, err)
                (Just (ab, s'), err) -> 
                    let (res, err2) = runParser (ab <$> pa) s' 
                    in (res, max err err2)

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
             (Nothing, err1) -> 
                case runParser y s of
                    (res, err2) -> (res, max err1 err2)
             res -> res

pAlternative :: Parser s e a -> Parser s e b -> Parser s e (Either a b)
pAlternative pl pr = (Left <$> pl) <<|> (Right <$> pr)

-- Parser that returns the current token without consuming it
peek :: Parser s e s
peek =
    Parser $ \case
        (ParserState cnt st@(a:_) fp con) -> (Just (a, ParserState cnt st fp con), Nothing)
        _ -> (Nothing, Nothing)

-- Create a parser that returns the current
-- token if `f` predicate is true
satisfy :: (s -> Bool) -> Parser s e s
satisfy f =
    Parser $ \case
                (ParserState cnt (a:rest) fp con) | f a ->
                    (Just (a, ParserState (cnt + 1) rest fp con), Nothing)
                _ -> (Nothing, Nothing)

-- Create a parser that returns the result of applying `f` 
-- to the current token. If Nothing is returned
-- then parser will fail.
satisfyAs :: (s -> Maybe b) -> Parser s e b
satisfyAs f = fromJust . f <$> satisfy (isJust . f)

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

-- Parse 2 elements exactly
pTwice :: Parser s e a -> Parser s e [a]
pTwice p = p <:> (pure <$> p)

-- Parse 0 or 1 element
pMaybe :: Parser s e a -> Parser s e (Maybe a)
pMaybe p = (Just <$> p) <<|> pure Nothing

-- Parse 0 or more elements 
pList :: Parser s e a -> Parser s e b -> Parser s e [a]
pList pElement pDelimiter =
    ((pure <$> pElement) <++> many' (pDelimiter *> pElement)) <<|> pure []

-- Parser that simply throws an error 
pError :: (ParserState s -> e) -> Parser s e a
pError err = Parser $ \s@(ParserState cnt _ fp con) -> (Nothing, Just (Error cnt (err s)))

-- Parser that simply throws an error 
pErrorMax :: (ParserState s -> e) -> Parser s e a
pErrorMax err = Parser $ \s@(ParserState cnt _ fp con) -> (Nothing, Just $ Error (cnt + 2) (err s))

-- Modify errors produced by the parser `p` using the function `err`
pWrapErrors :: (ParserState s -> e -> e) -> Parser s e a -> Parser s e a
pWrapErrors err p =
    Parser $ \s ->
        let xs = runParser p s in
            xs & _2._Just %~ (\(Error i e) -> Error i $ err s e)

-- Replace errors produced by the parser `p` using the function `err`
pReplaceError :: (ParserState s -> e) -> Parser s e a -> Parser s e a
pReplaceError err = pWrapErrors (\st _ -> err st)

sepBy1 :: Parser s e a -> Parser s e b -> Parser s e [a]
sepBy1 p sep = liftA2 (:) p (many' (sep *> p))

-- Not Parser -- succeeds if the given parser fails
pNot :: Parser s e a -> (ParserState s -> e) -> Parser s e ()
pNot p err = pReplaceError err (p *> pError err) <<|> pure ()

-- Parse non-associative operators.
-- Thus Sentences of the following format: 
-- p (`op` p)? and not: p `op` p `op` ...
pNonAssocOp :: (ParserState s -> e) -> Parser s e (a -> a -> a) -> Parser s e a -> Parser s e a
pNonAssocOp err op p = joinResult <$> p <*> (pMaybe ((,) <$> op <*> p <* pNot op err) <<|> (Nothing <$ pNot op err))
    where
        joinResult p Nothing = p
        joinResult p1 (Just (gen, p2)) = gen p1 p2

-- Parse sentences of the following format in a left associative way: 
-- p (`op` p)* => (((p `op` p) `op` p) `op` p)
pChainl :: Parser s e (a -> a -> a) -> Parser s e a -> Parser s e a
pChainl op p = foldl' (&) <$> p <*> many' (flip <$> op <*> p)

pChainlAlt :: (a -> a -> a) -> Parser s e a -> Parser s e b -> Parser s e a
pChainlAlt f p op = foldl1 f <$> sepBy1 p op

-- Parse sentences of the following format in a left associative way: 
-- p (`op` pc)* => (((p `op` pc) `op` pc) `op` p)
pChainl2 :: Parser s e (a -> b -> a) -> Parser s e b -> Parser s e a -> Parser s e a
pChainl2 op pc p = foldl' (&) <$> p <*> many' (flip <$> op <*> pc)

-- Parse sentences of the following format in a right associative way: 
-- p (`op` p)* => (p `op` (p `op` (p `op` p)))
pChainr :: Parser s e (a -> a -> a) -> Parser s e a -> Parser s e a
pChainr op p = (\a ma -> maybe a ($ a) ma) <$> p <*> pMaybe (flip <$> op <*> pChainr op p)

-- Parse sentences of the following format in a right associative way: 
-- op* p => op (op (op p))
pChainr1 :: Parser s e (a -> a) -> Parser s e a -> Parser s e a
pChainr1 op p = (op <*> pChainr1 op p) <<|> p
