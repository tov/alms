{-# LANGUAGE
      DeriveDataTypeable #-}
module Syntax.Lit (
  Lit(..)
) where

import Data.Generics (Typeable, Data)

-- | Literals
data Lit
  = LtInt Integer
  | LtStr String
  | LtFloat Double
  deriving (Eq, Typeable, Data)
