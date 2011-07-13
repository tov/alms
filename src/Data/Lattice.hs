{-# LANGUAGE
      FlexibleInstances,
      UndecidableInstances,
      UnicodeSyntax #-}
module Data.Lattice (
  -- * Lattices
  Lattice(..), BoundedLattice(..),
  -- ** Dual lattices
  DUAL(..),
) where

import Util

import Prelude ()
import qualified Data.Set as S

-- | Lattices.
--  Minimal complete definition is '(⊔)' and '(⊓)'.
class Eq a ⇒ Lattice a where
  (⊔), (⊓) ∷ a → a → a
  (⊑), (⊒) ∷ a → a → Bool
  a ⊑ b = a ⊔ b == b
  a ⊒ b = b ⊑ a

infixl 6 ⊔
infixl 7 ⊓
infix 4 ⊑, ⊒

-- | Bounded lattices are 'Lattice's that are 'Bounded'.
class (Bounded a, Lattice a) ⇒ BoundedLattice a where
  bigJoin, bigMeet ∷ [a] → a

instance (Bounded a, Lattice a) ⇒ BoundedLattice a where
  bigJoin = foldr (⊔) minBound
  bigMeet = foldr (⊓) maxBound

-- 'Nothing' is a new point.
instance Lattice a ⇒ Lattice (Maybe a) where
  Just a  ⊔ Just b  = Just (a ⊔ b)
  Nothing ⊔ b       = b
  a       ⊔ Nothing = a
  Just a  ⊓ Just b  = Just (a ⊓ b)
  Nothing ⊓ _       = Nothing
  _       ⊓ Nothing = Nothing

instance Ord a ⇒ Lattice (S.Set a) where
  (⊔) = S.union
  (⊓) = S.intersection
  (⊑) = S.isSubsetOf

instance (Lattice a, Lattice b) ⇒ Lattice (a, b) where
  (a, b) ⊔ (a', b') = (a ⊔ a', b ⊔ b')
  (a, b) ⊓ (a', b') = (a ⊓ a', b ⊓ b')
  (a, b) ⊑ (a', b') = a ⊑ a' && b ⊑ b'

instance (Lattice a, Lattice b, Lattice c) ⇒ Lattice (a, b, c) where
  (a, b, c) ⊔ (a', b', c') = (a ⊔ a', b ⊔ b', c ⊔ c')
  (a, b, c) ⊓ (a', b', c') = (a ⊓ a', b ⊓ b', c ⊓ c')
  (a, b, c) ⊑ (a', b', c') = a ⊑ a' && b ⊑ b' && c ⊑ c'

-- | Injection for the dual lattice.
newtype DUAL a = DUAL { dual ∷ a } deriving (Eq, Show)

instance Lattice a ⇒ Lattice (DUAL a) where
  DUAL a ⊔ DUAL b = DUAL (a ⊓ b)
  DUAL a ⊓ DUAL b = DUAL (a ⊔ b)

instance Bounded a ⇒ Bounded (DUAL a) where
  minBound = DUAL maxBound
  maxBound = DUAL minBound

instance Ord a ⇒  Ord (DUAL a) where
  DUAL a `compare` DUAL b = b `compare` a
