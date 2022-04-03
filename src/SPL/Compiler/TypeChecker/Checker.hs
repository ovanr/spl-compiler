{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SPL.Compiler.TypeChecker.Checker where

import System.Random
import Control.Monad.Random.Class
import Control.Monad.State.Class
import Data.Function ((&))

newtype Error e = Error { msg :: e }

newtype SRE e s a = 
    SRE { runSRE :: s -> StdGen -> (Either e a, s, StdGen) }
    deriving (Functor)

instance Applicative (SRE e s) where
    pure a = SRE $ \s g -> (Right a, s, g)
    (SRE fab) <*> (SRE fa) = SRE $ 
        \s g -> let (eab, !s', g') = fab s g
                    (ea, !s'', g'') = fa s' g'
                in (eab <*> ea, s'', g'')

instance Monad (SRE e s) where
    return = pure
    (SRE ma) >>= amb = SRE $ 
        \s g -> let (ea, !s', g') = ma s g 
                in case ea of
                    Left !e -> (Left e, s', g')
                    Right !a -> runSRE (amb a) s' g'
                
instance MonadState s (SRE e s) where
    get = SRE $ \s g -> (Right s, s, g)
    put s = SRE $ \_ g -> (Right (), s, g)
    state st = SRE $ \s g -> let (!a, !s') = st s in (Right a, s', g)

instance MonadRandom (SRE e s) where
    getRandom = SRE $ 
        \s g -> let (!a, g') = random g
                in (Right a, s, g')
    getRandoms = SRE $ 
        \s g -> let (g', g'') = split g
                    as = randoms g'
                in (Right as, s, g'')
    getRandomR range = SRE $ 
        \s g -> let (!a, g') = randomR range g
                in (Right a, s, g')
    getRandomRs range = SRE $ 
        \s g -> let (g', g'') = split g
                    as = randomRs range g'
                in (Right as, s, g'')
