module AST.Lit (
  Lit(..)
) where

import AST.Anti

import Data.Generics (Typeable, Data)

-- | Literals
data Lit
  = LtInt Integer
  | LtChar Char
  | LtStr String
  | LtFloat Double
  | LtAnti Anti
  deriving (Eq, Typeable, Data)
