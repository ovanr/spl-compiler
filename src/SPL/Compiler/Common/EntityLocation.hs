{-# LANGUAGE TemplateHaskell #-}
module SPL.Compiler.Common.EntityLocation where

import Control.Lens
import Numeric.Natural
import qualified Data.Text as T

import SPL.Compiler.Lexer.AlexLexGen (AlexPosn(..), Token(..), SPLToken(..), Keyword(..), Type(..))

-- Location is (LineNum, ColumnNum)
type Location = (Natural, Natural)

-- EntityLoc is StartLocation and EndLocation in source file
data EntityLoc = EntityLoc {
    _locStart :: Location,
    _locEnd :: Location
} deriving (Eq, Ord, Show)

makeLenses ''EntityLoc

instance Semigroup EntityLoc where
    (EntityLoc start1 end1) <> (EntityLoc start2 end2) = 
        EntityLoc (max start1 start2) (max end1 end2)

instance Monoid EntityLoc where
    mempty = EntityLoc (0,0) (0,0)
    mappend = (<>)

class Locatable a where
    getLoc :: a -> EntityLoc
    setLoc :: EntityLoc -> a -> a

    getStartLoc :: a -> Location
    getStartLoc a = getLoc a ^. locStart

    getEndLoc :: a -> Location
    getEndLoc a = getLoc a ^. locEnd

instance Locatable EntityLoc where
    setLoc e _ = e
    getLoc = id

instance Locatable a => Locatable [a] where
    setLoc l = map (setLoc l)
    getLoc [] = mempty
    getLoc list = EntityLoc (getStartLoc $ head list) (getEndLoc $ last list)

locationRange :: EntityLoc -> EntityLoc -> EntityLoc 
locationRange (EntityLoc start _) (EntityLoc _ end) = EntityLoc start end

infixr 5 |-|
(|-|) :: (Locatable a, Locatable b) => a -> b -> EntityLoc
start |-| end = EntityLoc (getStartLoc start) (getEndLoc end)

instance Locatable Token where
    setLoc _ EOF = EOF
    setLoc (EntityLoc (sl, sc) (el, ec)) (MkToken (AlexPn _ l c) t) = 
        MkToken (AlexPn (fromIntegral $ el*ec) (fromIntegral sl) (fromIntegral sc)) t
    getLoc (MkToken (AlexPn _ l c) t) = 
        EntityLoc (l', c') (l', fromIntegral $ c + tokenLength t)
        where
            l' = fromIntegral l
            c' = fromIntegral c
            tokenLength (KeywordToken v) = length $ show v
            tokenLength (TypeToken v) = length (show v)
            tokenLength (IntToken i) = length (show i)
            tokenLength (IdentifierToken v) = T.length v
            tokenLength (StringToken str) = T.length str + 2
            tokenLength (BoolToken v) = length $ show v
            tokenLength (CharToken _) = 1
            tokenLength (SymbolToken _) = 1
    getLoc _ = error "Match on EOF"
