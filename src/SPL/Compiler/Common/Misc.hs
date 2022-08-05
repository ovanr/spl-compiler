{-# LANGUAGE RankNTypes #-}

module SPL.Compiler.Common.Misc where

import Control.Monad.State
import Control.Applicative (liftA2)
import GHC.Base (liftA3)
import Control.Lens (Lens', (.~), (^.))
import Control.Lens.Lens ((&))

wrapStateT :: (Monad m, MonadState s m) => (s -> s) -> (s -> s -> s) -> m a -> m a
wrapStateT to from st = do
    initialState <- get
    modify to
    a <- st
    modify (from initialState)
    return a

inSandboxedState :: MonadState s m => Lens' s a -> a -> m b -> m b
inSandboxedState lens x = wrapStateT
                               (lens .~ x)
                               (\old new -> new & lens .~ (old ^. lens))

impossible :: a
impossible = error "impossible happened!"

intercalateM :: Applicative f => f a -> [f a] -> f [a]
intercalateM _ [] = pure []
intercalateM _ [x] = pure <$> x
intercalateM sep (x:y:xs) = liftA3 (\a b c -> a : b : c) x sep (intercalateM y xs)
