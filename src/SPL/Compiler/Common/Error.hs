{-# LANGUAGE OverloadedStrings #-}
module SPL.Compiler.Common.Error where

import SPL.Compiler.Common.EntityLocation

import Control.Monad.State
import Data.Text (Text)
import Control.Lens ((^?), ix)
import qualified Data.Text as T

class ContainsSource s where
    getFilePath :: s -> FilePath
    getSource :: s -> [Text]

definition :: (Locatable a, MonadState s m, ContainsSource s) => Text -> a -> m [Text]
definition err elem = do
    fp <- gets getFilePath 
    con <- gets getSource 

    let lineNum = fst $ getStartLoc elem
        someLine = con ^? ix (fromIntegral $ lineNum - 1)
        startCol = fromIntegral $ snd $ getStartLoc elem
        endCol = fromIntegral $ snd $ getEndLoc elem
        header = T.pack fp <> ":" <> T.pack (show lineNum) <> ":" <>
                 T.pack (show startCol) <> ": " <> err

    case someLine of
       Nothing -> pure ["Sorry, I am unable to retrieve the location of the error"]
       Just line ->
            let bottomHighlight = T.replicate startCol " " <> T.replicate (endCol - startCol) "^"
                leftMargin = T.pack (show lineNum) <> " "
                emptyLeftMargin = T.replicate (T.length leftMargin) " " <> "|"
            in pure [
                 T.unlines
                 [header,
                  emptyLeftMargin,
                  leftMargin <> "| " <> line,
                  emptyLeftMargin <> bottomHighlight
                 ]
               ]
