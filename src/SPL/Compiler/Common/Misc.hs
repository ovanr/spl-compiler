
module SPL.Compiler.Common.Misc where

import Control.Monad.State

wrapStateT :: Monad m => (s -> s) -> (s -> s -> s) -> StateT s m a -> StateT s m a
wrapStateT to from st = do
    initialState <- get
    modify to
    a <- st
    modify (from initialState)
    return a

impossible :: a
impossible = error "impossible happened!"
