module Alt.Parsec (
  module Text.ParserCombinators.Parsec,
) where

import Text.ParserCombinators.Parsec hiding ((<|>), many, optional)

#if PARSEC_VERSION == 2
import qualified Text.ParserCombinators.Parsec as Parsec
import Control.Applicative
import Control.Monad

-- | Parsec parsers are Applicatives, which lets us write slightly
--   more pleasant, non-monadic-looking parsers
instance Applicative (GenParser a b) where
  pure  = return
  (<*>) = ap

instance Alternative (GenParser a b) where
  empty = pzero
  (<|>) = (Parsec.<|>)
#endif
