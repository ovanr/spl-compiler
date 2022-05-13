
module SPL.Compiler.SemanticAnalysis.TypeCheck.TCon where

import SPL.Compiler.Common.Error
import Data.Maybe (fromMaybe)
import Control.Lens
import Control.Monad.State
import qualified Data.List as L
import qualified Data.Text as T

import SPL.Compiler.SemanticAnalysis.TCT
import SPL.Compiler.SemanticAnalysis.TypeCheck.Unify
import SPL.Compiler.SemanticAnalysis.TCTEntityLocation

addTCon :: TCon -> TCMonad ()
addTCon tcon = modify (\st -> st & getTcons %~ (L.nub . (tcon :)))

tconError tcon = do
    let header = T.pack $ "Unable to find an instance for " <> show tcon
    err <- definition (T.pack $ "'" <>
                       show tcon <>
                       "' instance has been inferred for: ") tcon
    return $ header : err

validateTCon :: [TCon] -> TCMonad ()
validateTCon tcons = use getSubst >>= (\s -> validateTCon' (s $* tcons))
    where
        validateTCon' [] = return ()
        validateTCon' (t@(TEq TCTFunType{}):_) = tconError t >>= tcError
        validateTCon' (TEq _:xs) = validateTCon' xs
        validateTCon' (t@(TOrd TCTFunType{}):_) = tconError t >>= tcError
        validateTCon' (TOrd _:xs) = validateTCon' xs
        validateTCon' (t@(TPrint TCTFunType{}):_) = tconError t >>= tcError
        validateTCon' ((TPrint _):xs) = validateTCon' xs

