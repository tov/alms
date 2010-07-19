{-# LANGUAGE
      EmptyDataDecls,
      GADTs
      #-}
module Message.AST (
  Message(..),
  V, H, MessageV, MessageH,
  StackStyle(..)
) where

import PprClass

-- | Simple message markup
data Message d where
  Words     :: String -> Message d
  Flow      :: [Message H] -> Message d
  Exact     :: String -> Message d
  Surround  :: String -> String -> Message d -> Message d
  Quote     :: Message d -> Message d
  Block     :: Message H -> Message V
  Stack     :: StackStyle -> [Message V] -> Message V
  Table     :: [(String, Message V)] -> Message V
  Indent    :: Message V -> Message V
  Printable :: Ppr a => a -> Message d
  Showable  :: Show a => a -> Message d
  AntiMsg   :: String -> String -> Message d

data V
data H

-- | Vertical mode message
type MessageV = Message V

-- | Horizontal mode message
type MessageH = Message H

-- | Types of lists
data StackStyle
  = Numbered
  | Bulleted
  | Separated
  | Broken

