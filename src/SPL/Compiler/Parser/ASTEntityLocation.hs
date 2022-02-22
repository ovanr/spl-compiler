
module SPL.Compiler.Parser.ASTEntityLocation where

import SPL.Compiler.Lexer.AlexLexGen (AlexPosn(..), Token(..), SPLToken(..), Keyword(..), Type(..))
import SPL.Compiler.Parser.AST
import qualified Data.Text as T
import Control.Lens ((^.), _Just)

class Locatable a where
    --setLoc :: EntityLoc -> a            Does not make sense for debugging later on
    getLoc :: a -> EntityLoc

    getStartLoc :: a -> Location
    getStartLoc a = getLoc a ^. locStart

    getEndLoc :: a -> Location
    getEndLoc a = getLoc a ^. locEnd

instance Locatable ASTIdentifier where
    getLoc (ASTIdentifier l _) = l

instance Locatable ASTFunCall where
    getLoc (ASTFunCall l _ _) = l

instance Locatable ASTExpr where
    getLoc (IdentifierExpr (ASTIdentifier l _)) = l
    getLoc (IntExpr l _) = l
    getLoc (CharExpr l _) = l
    getLoc (BoolExpr l _) = l
    getLoc (FunCallExpr (ASTFunCall l _ _)) = l
    getLoc (OpExpr l _ _) = l 
    getLoc (Op2Expr l _ _ _) = l  
    getLoc (EmptyListExpr l) = l
    getLoc (TupExpr l _ _) = l
    
instance Locatable Token where
    getLoc (MkToken (AlexPn _ l c) t) = EntityLoc (l,c) (l, c + tokenLength t)
        where
            tokenLength (KeywordToken v) = length $ show v
            tokenLength (TypeToken v) = length (show v) - 4
            tokenLength (IntToken i) = length $ show i
            tokenLength (IdentifierToken v) = T.length v
            tokenLength (BoolToken v) = length $ show v
            tokenLength (CharToken _) = 1
            tokenLength (SymbolToken _) = 1
    getLoc _ = error "Match on EOF"

instance Locatable a => Locatable [a] where
    getLoc list = EntityLoc (getStartLoc $ head list) (getEndLoc $ last list)

locationRange :: EntityLoc -> EntityLoc -> EntityLoc 
locationRange (EntityLoc start _) (EntityLoc _ end) = EntityLoc start end

infixr 5 |-|
(|-|) :: Locatable a => Locatable b => a -> b -> EntityLoc
start |-| end = EntityLoc (getStartLoc start) (getEndLoc end)