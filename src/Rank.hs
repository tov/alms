{-# LANGUAGE
      UnicodeSyntax
      #-}
module Rank (
  Rank, zero, infinity, inc
) where

import Data.Monoid
import PprClass as Ppr

data Rank
  = Finite !Int
  | Infinity
  deriving (Eq, Ord)

instance Show Rank where
  show (Finite n) = show n
  show Infinity   = "∞"

instance Ppr Rank where ppr = Ppr.text . show

instance Monoid Rank where
  mempty  = Finite 0
  mappend = min

instance Bounded Rank where
  minBound = Finite 0
  maxBound = Infinity

zero, infinity ∷ Rank
zero     = minBound
infinity = maxBound

inc ∷ Rank → Rank
inc (Finite n) = Finite (n + 1)
inc Infinity   = Infinity
