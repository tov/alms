module Type.Rank (
  Rank, zero, infinity, inc
) where

import Syntax.PprClass as Ppr

import Data.Generics (Typeable, Data)

data Rank
  = Finite !Int
  | Infinity
  deriving (Eq, Ord, Typeable, Data)

instance Show Rank where
  show (Finite n) = show n
  show Infinity   = "∞"

instance Ppr Rank where ppr = Ppr.text . show

instance Bounded Rank where
  minBound = Finite 0
  maxBound = Infinity

zero, infinity ∷ Rank
zero     = minBound
infinity = maxBound

inc ∷ Rank → Rank
inc (Finite n) = Finite (n + 1)
inc Infinity   = Infinity
