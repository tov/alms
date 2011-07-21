module Type.TyVar (
  -- * Type variable observations
  Tv(..), Kind(..), Flavor(..),
  tvFlavorIs, tvKindIs, uglyTvName,
  -- * Miscellany
  varianceToKind,
  -- * Free type variables
  Ftv(..), VarMap,
  FtvTree(..), foldFtvTree,
) where

import Util
import Syntax.PprClass
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

instance Ppr Kind where
  ppr KdType = char '*'
  ppr KdQual = char 'Q'
instance Show Kind where showsPrec = showFromPpr

-- | Get the kind associated with type variables that appear at a
--   particular variance.
varianceToKind ∷ Variance → Kind
varianceToKind var = if isQVariance var then KdQual else KdType

-- | Flavors of type variables
data Flavor
  -- | unification variables
  = Universal
  -- | existential skolems
  | Existential
  -- | universal skolems
  | Skolem
  deriving (Eq, Typeable, Data)

instance Ppr Flavor where ppr = char . flavorSigil
instance Show Flavor where showsPrec = showFromPpr

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
  -- | A description
  tvDescr       ∷ tv → Doc
  -- | Read the contents of a type variable (not pure)
  unsafeReadTV  ∷ tv → Maybe (Type tv)

instance Tv Empty where
  tvUniqueID    = elimEmpty
  tvKind        = elimEmpty
  tvFlavor      = elimEmpty
  tvQual        = elimEmpty
  tvDescr       = elimEmpty
  unsafeReadTV  = elimEmpty

instance Ftv Empty Empty where ftvTree = elimEmpty
instance Ppr Empty       where ppr = elimEmpty

instance Tv Int where
  tvUniqueID    = id
  tvKind _      = KdType
  tvFlavor _    = Skolem
  tvQual _      = Nothing
  tvDescr       = ppr
  unsafeReadTV  = const Nothing

instance Ftv Int Int where ftvTree = FTSingle

-- | Check the flavor of a type variable
tvFlavorIs ∷ Tv tv ⇒ Flavor → tv → Bool
tvFlavorIs flavor v = tvFlavor v == flavor

-- | Check the kind of a type variable
tvKindIs ∷ Tv tv ⇒ Kind → tv → Bool
tvKindIs kind v = tvKind v == kind

-- | When all else fails, we can print a type variable like this
uglyTvName ∷ Tv tv ⇒ tv → String
uglyTvName tv = flavorSigil (tvFlavor tv) : show (tvUniqueID tv) where

-- | A character denoting a flavor
flavorSigil ∷ Flavor → Char
flavorSigil Universal   = '?'
flavorSigil Existential = '#'
flavorSigil Skolem      = '$'

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
  | FTVariance VarianceEndo (FtvTree v)
  -- | Indicates that the subtree is guarded by a type constructor
  --   that allows recursion
  | FTGuard (FtvTree v)
  -- | A forest of 'FtvTree's
  | FTBranch [FtvTree v]
  deriving (Functor, Show)

-- | Type for providing a 'Show' instance for @Variance -> Variance@
-- functions which allows deriving 'Show' for 'FtvTree'.
newtype VarianceEndo
  = VarianceEndo { applyVarianceEndo ∷ Variance → Variance }

instance Show VarianceEndo where
  show ve = show (applyVarianceEndo ve 1)

instance Monoid (FtvTree v) where
  mempty      = FTBranch []
  mappend a b = FTBranch [a, b]
  mconcat     = FTBranch

-- | A fold for 'FtvTree's. It's necessary to specify how to
--   add a free type variable and its variance to the result, and the
--   initial result.  Note that this fold gives no information about
--   the shape of the tree, but it uses the tree structure to determine
--   the variance of each type variable.
foldFtvTree ∷ (v → Variance → Bool → r → r) → r → FtvTree v → r
foldFtvTree fsingle = loop Covariant False where
  loop var gua acc tree = case tree of
    FTSingle v      → fsingle v var gua acc
    FTVariance vf t → loop (applyVarianceEndo vf var) gua acc t
    FTGuard t       → loop var True acc t
    FTBranch ts     → foldr (flip (loop var gua)) acc ts

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
  ftvFold  ∷ (tv → Variance → Bool → r → r) → r → a → r
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
  ftvFold fsingle zero a
                 = foldFtvTree fsingle zero $ ftvTree a
  ftvV           = ftvFold (const <$$> M.insertWith (+)) M.empty
  ftvG           = ftvFold (const <$> M.insertWith (&&)) M.empty
  ftvSet         = ftvFold (\v _ _ → S.insert v) S.empty
  ftvList        = S.toAscList . ftvSet

instance Ord tv ⇒ Ftv (Type tv) tv where
  ftvTree = foldType
              (mkQuF (\_ _ → id))
              (mkBvF (\_ _ _ → mempty))
              FTSingle
              (\tc trees → FTBranch
                 [ FTVariance (VarianceEndo (* var)) $
                     if guarded then FTGuard tree else tree
                 | tree    ← trees
                 | var     ← tcArity tc
                 | guarded ← tcGuards tc ])
              (\_ σ1 σ2 → FTBranch [FTGuard σ1, σ2])
              (mkMuF (\_ → id))

instance Ord tv ⇒ Ftv (QExp tv) tv where
  ftvTree QeA      = FTBranch []
  ftvTree (QeU αs) = FTBranch (FTSingle <$> S.toList αs)
  ftvSet QeA       = S.empty
  ftvSet (QeU αs)  = αs

instance Ftv a tv ⇒ Ftv [a] tv where
  ftvTree = foldMap ftvTree

instance Ftv a tv ⇒ Ftv (M.Map k a) tv where
  ftvTree = ftvTree . M.elems

instance (Ftv a tv, Ftv b tv) ⇒ Ftv (a, b) tv where
  ftvTree (a, b) = ftvTree a `mappend` ftvTree b

instance (Ftv a tv, Ftv b tv, Ftv c tv) ⇒ Ftv (a, b, c) tv where
  ftvTree (a, b, c) = mconcat [ftvTree a, ftvTree b, ftvTree c]

instance (Ftv a tv, Ftv b tv, Ftv c tv, Ftv d tv) ⇒ Ftv (a, b, c, d) tv where
  ftvTree (a, b, c, d) = mconcat [ftvTree a, ftvTree b, ftvTree c, ftvTree d]

instance Ftv a tv ⇒ Ftv (Maybe a) tv where
  ftvTree = maybe mempty ftvTree

instance (Ftv a tv, Ftv b tv) ⇒ Ftv (Either a b) tv where
  ftvTree = either ftvTree ftvTree

