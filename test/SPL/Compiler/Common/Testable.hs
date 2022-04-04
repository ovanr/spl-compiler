
module SPL.Compiler.Common.Testable where

import SPL.Compiler.Lexer.AlexLexGen (Token(..), SPLToken(..), AlexPosn(..), Type(..), Keyword(..))
import SPL.Compiler.Common.EntityLocation
import Data.Default

-- used for test purposes
-- transform a data type to its test form
-- this means that certain fields may be replaced
-- with their default values for ease of comparisons, etc.
class Testable a where
    toTestForm :: a -> a

instance Default EntityLoc where
    def = EntityLoc (1,1) (1,1)

instance Default AlexPosn where
    def = AlexPn 0 1 1

instance Testable a => Testable [a] where
    toTestForm = map toTestForm

instance Testable a => Testable (Maybe a) where
    toTestForm (Just val) = Just (toTestForm val)
    toTestForm Nothing = Nothing

instance Testable a => Testable (Either b a) where
    toTestForm (Left val) = Left val
    toTestForm (Right val) = Right (toTestForm val)
