{-# LANGUAGE
      DeriveDataTypeable,
      DeriveFunctor,
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
import qualified Data.Map as M
import qualified Data.Set as S

---
--- TYPE VARIABLES
---

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

instance Ftv Empty Empty where ftvTree = elimEmpty
instance Ppr Empty       where ppr = elimEmpty

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

---
--- FREE TYPE VARIABLES
---

{-
  We're going to construct a framework for generic functions to compute
  the free type variables of a type.  It may seem a bit over-engineered,
  but it turns out to be handy, The idea is to write a generic function
  that builds an 'FtvTree', which contains all the free type variables
  in the relevant piece of syntax, along with variance and recursive
  guard information.
-}

-- | A tree of free type variables, with variance and recursive guard
--   information
data FtvTree v
  -- | A single free type variable
  = FTSingle v
  -- | Updates the incoming variance to give the variance in
  --   the subtree
  | FTVariance (Variance → Variance) (FtvTree v)
  -- | Indicates that the subtree is guarded by a type constructor
  --   that allows recursion
  | FTGuard (FtvTree v)
  -- | A forest of 'FtvTree's
  | FTBranch [FtvTree v]
  deriving Functor

instance Monoid (FtvTree v) where
  mempty      = FTBranch []
  mappend a b = FTBranch [a, b]
  mconcat     = FTBranch

-- | A fold for 'FtvTree's. It's necessary to specify how to
--   add a free type variable and its variance to the result, and the
--   initial result.  Note that this fold gives no information about
--   the shape of the tree, but it uses the tree structure to determine
--   the variance of each type variable.
foldFtvTree ∷ (v → Variance → r → r) → (r → r) → r → FtvTree v → r
foldFtvTree fsingle fguard = loop Covariant where
  loop var acc (FTSingle v)       = fsingle v var acc
  loop var acc (FTVariance vf t)  = loop (vf var) acc t
  loop var acc (FTGuard t)        = fguard (loop var acc t)
  loop var acc (FTBranch ts)      = foldr (flip (loop var)) acc ts

-- | Map from variables to variances
type VarMap v = M.Map v Variance

class Ord tv ⇒ Ftv a tv | a → tv where
  -- | To compute the 'FtvTree' for a piece of syntax.  Because
  --   everything is parametric in the representation of ftvs, it needs
  --   to be told how to dereference an apparently free type variable.
  --   The dereferencing function should return @Nothing@ if the type
  --   variable is actually free, and @Just τ@ if a type @τ@ has been
  --   substituted for it.
  --
  --   This is the only method that doesn't have a default
  --   implementation, so it must be defined explicitly.
  ftvTree  ∷ a → FtvTree tv
  -- | To fold over the free type variables in a piece of syntax.
  ftvFold  ∷ (tv → Variance → r → r) → (r → r) → r → a → r
  -- | To get a map from free type variables to their variances.
  ftvV     ∷ a → VarMap tv
  -- | To get a map from free type variables to their guardedness
  ftvG     ∷ a → M.Map tv Bool
  -- | To get a map from free type variables to a list of all their
  --   occurrences' variances.
  ftvSet   ∷ a → S.Set tv
  -- | To get a list of the free type variables in a type (with no repeats).
  ftvList  ∷ a → [tv]
  --
  --
  ftvFold fsingle fguard zero a
                 = foldFtvTree fsingle fguard zero $ ftvTree a
  ftvV           = ftvFold (M.insertWith (+)) id M.empty
  ftvG           = ftvFold (\v _ → M.insert v False) (True <$) M.empty
  ftvSet         = ftvFold (const . S.insert) id S.empty
  ftvList        = S.toAscList . ftvSet

