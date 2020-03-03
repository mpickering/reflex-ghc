{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Main where


import GHC.RTS.Events

import Data.Word
import Data.Text (Text)
import System.Environment
import Data.Maybe
import Control.Monad
import Data.Char

import Data.Version
import Text.ParserCombinators.ReadP
import Debug.Trace

import Data.Map (fromListWith, toList)
import Data.List
import Data.Ord

frequency :: (Ord a) => [a] -> [(a, Int)]
frequency xs = sortBy (comparing snd) $ toList (fromListWith (+) [(x, 1) | x <- xs])

main = entry

entry :: IO ()
entry = do
  fps <- getArgs
  case fps of
    [fp] -> do
      el <- either error id <$> readEventLogFromFile fp
      let (EventLog _ (Data es)) = el
      analyse el

    _ -> error "Usage: hs-speedscope program.eventlog"

analyse :: EventLog -> IO ()
analyse (EventLog _h (Data (sortOn evTime -> es))) =
  mapM_ print (frequency ss)
  where
    (EL (fromMaybe "" -> profile_name) el_version ss) =
      foldl' (flip processEvents) initEL es

    initEL = EL Nothing Nothing []


    processEvents :: Event -> EL -> EL
    processEvents (Event _t ei _c) el =
      case ei of
        ProgramArgs _ (pname: _args) ->
          (el { prog_name = Just pname })
        RtsIdentifier _ rts_ident ->
          (el { rts_version = parseIdent rts_ident })
        UserMessage s -> el { msgs = s : (msgs el) }
        _ -> el

parseIdent :: String -> Maybe (Version, String)
parseIdent s = listToMaybe $ flip readP_to_S s $ do
  void $ string "GHC-"
  [v1, v2, v3] <- replicateM 3 (intP <* optional (char '.'))
  skipSpaces
  return (makeVersion [v1,v2,v3])
  where
    intP = do
      x <- munch1 isDigit
      return $ read x

data EL = EL {
    prog_name :: Maybe String
    , rts_version :: Maybe (Version, String)
    , msgs :: ![String]
}
