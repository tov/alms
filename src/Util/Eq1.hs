{-# LANGUAGE
      UnicodeSyntax
      #-}
{- Equality type classes for unary and binary type constructors. -}
module Util.Eq1 (
  Eq1(..), EQ1(..),
) where

import Data.IORef
import Data.STRef
import Control.Concurrent.STM.TVar

-- | Like 'Eq', but for unary type constructors.
class Eq1 t where
  eq1 ∷ t a → t a → Bool
  ne1 ∷ t a → t a → Bool
  x `ne1` y = not (x `eq1` y)

infix 4 `eq1`, `ne1`

instance Eq1 IORef where eq1 = (==)
instance Eq1 (STRef s) where eq1 = (==)
instance Eq1 TVar where eq1 = (==)

-- | Injection for using 'Eq': If @t@ is 'Eq1' then @EQ1 t a@ is 'Eq'
newtype EQ1 t a = EQ1 (t a)
instance Eq1 t ⇒ Eq1 (EQ1 t) where EQ1 x `eq1` EQ1 y = x `eq1` y
instance Eq1 t ⇒ Eq (EQ1 t a) where EQ1 x == EQ1 y = x `eq1` y

