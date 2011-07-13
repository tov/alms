{-# LANGUAGE
      EmptyDataDecls,
      GADTs
      #-}
module Message.AST (
  Message(..),
  H, V, StackStyle(..),
  wordsMsg, quoteMsg, pprMsg, showMsg, emptyMsg,
) where

import Syntax.PprClass

-- | Simple message markup
data Message d where
  Words     :: String -> Message d
  Flow      :: [Message H] -> Message d
  Exact     :: String -> Message d
  Surround  :: String -> String -> Message d -> Message d
  Quote     :: Message d -> Message d
  Stack     :: StackStyle -> [Message V] -> Message V
  Table     :: [(String, Message V)] -> Message V
  Indent    :: Message V -> Message V
  Printable :: Ppr a => Int -> a -> Message d
  Showable  :: Show a => a -> Message d
  AntiMsg   :: String -> String -> Message d

data H
data V

-- | Types of lists
data StackStyle
  = Numbered
  | Bulleted
  | Separated
  | Broken

--
-- Public AST builders
--

wordsMsg :: String -> Message d
wordsMsg  = Words

quoteMsg :: Message d -> Message d
quoteMsg  = Quote

pprMsg   :: Ppr a => a -> Message d
pprMsg    = Printable (-1)

showMsg  :: Show a => a -> Message d
showMsg   = Showable

emptyMsg :: Message d
emptyMsg  = Words ""

