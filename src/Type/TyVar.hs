{-# LANGUAGE
      DeriveDataTypeable,
      FunctionalDependencies,
      MultiParamTypeClasses,
      UnicodeSyntax
    #-}
module Type.TyVar (
  -- * Type variable observations
  Tv(..), Kind(..), Flavor(..),
  tvFlavorIs, tvKindIs, uglyTvName,
) where

import Util
import PprClass
import Type.Internal

import Prelude ()
import Data.Generics (Typeable, Data)

-- | Internal kinds for type variables
data Kind
  -- | The kind of normal types
  = KdType
  -- | The kind of qualifier variables
  | KdQual
  deriving (Eq, Typeable, Data)

-- | Flavors of type variables
data Flavor
  -- | unification variables
  = Universal
  -- | existential skolems
  | Existential
  -- | universal skolems
  | Skolem
  deriving (Eq, Typeable, Data)

-- | Type variable observations
class (Ftv tv tv, Show tv, Ppr tv) ⇒ Tv tv where
  -- | The unique identity of a type variable
  tvUniqueID    ∷ tv → Int
  -- | The internal kind of a type variable
  tvKind        ∷ tv → Kind
  -- | The internal flavor of a type variable
  tvFlavor      ∷ tv → Flavor
  -- | Possibly a qualifier bound
  tvQual        ∷ tv → Maybe QLit

instance Tv Empty where
  tvUniqueID    = elimEmpty
  tvKind        = elimEmpty
  tvFlavor      = elimEmpty
  tvQual        = elimEmpty

-- | Check the flavor of a type variable
tvFlavorIs ∷ Tv tv ⇒ Flavor → tv → Bool
tvFlavorIs flavor v = tvFlavor v == flavor

-- | Check the kind of a type variable
tvKindIs ∷ Tv tv ⇒ Kind → tv → Bool
tvKindIs kind v = tvKind v == kind

-- | When all else fails, we can print a type variable like this
uglyTvName ∷ Tv tv ⇒ tv → String
uglyTvName tv = sigil : '.' : show (tvUniqueID tv) where
  sigil = case tvFlavor tv of
    Universal   → '?'
    Existential → '#'
    Skolem      → '$'

class Ord tv ⇒ Ftv a tv | a → tv where

instance Ftv Empty Empty where
instance Ppr Empty where ppr = elimEmpty
