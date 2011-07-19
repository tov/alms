{-# LANGUAGE
      FlexibleContexts,
      FlexibleInstances,
      FunctionalDependencies,
      MultiParamTypeClasses,
      QuasiQuotes,
      TupleSections,
      UndecidableInstances,
      UnicodeSyntax
    #-}
-- | Instantiation and generalization
module Statics.InstGen (
  -- * Instantiation operations
  instantiate, instantiateNeg, instAllEx, instAll, instEx,
  -- * Type-matching instantiation
  splitCon, splitRow,
  -- * Conditional generalization/instantiation
  Request(..), MkRequest(..),
  maybeGen, maybeInstGen, checkEscapingEx,
  -- * Instantiating type annotation variables
  withTVsOf,
) where

import Util
import qualified AST
import AST.TypeAnnotation
import qualified Syntax.Ppr as Ppr
import qualified Type.Rank as Rank
import Type
import Statics.Env
import Statics.Error
import Statics.Constraint

import Prelude ()
import qualified Data.Map as M

---
--- INSTANTIATION OPERATIONS
---

-- | To instantiate a prenex quantifier with fresh type variables.
instantiate ∷ MonadConstraint tv r m ⇒ Type tv → m (Type tv)
instantiate = instAllEx True True

-- | To instantiate a prenex quantifier with fresh type variables, in
--   a negative position
instantiateNeg ∷ MonadConstraint tv r m ⇒ Type tv → m (Type tv)
instantiateNeg = instAllEx False False

-- | Instantiate the outermost universal and existential quantifiers
--   at the given polarities.
instAllEx ∷ MonadConstraint tv r m ⇒ Bool → Bool → Type tv → m (Type tv)
instAllEx upos epos = subst >=> instEx epos >=> instAll upos

-- | Instantiate an outer universal quantifier.
--   PRECONDITION: σ is fully substituted.
instAll ∷ MonadConstraint tv r m ⇒ Bool → Type tv → m (Type tv)
instAll pos (TyQu Forall αqs σ) = do
  traceN 4 ("instAll/∀", pos, αqs, σ)
  instGeneric 0 (determineFlavor Forall pos) αqs σ
instAll pos (TyQu Exists αqs (TyQu Forall βqs σ)) = do
  traceN 4 ("instAll/∃∀", pos, αqs, βqs, σ)
  TyQu Exists αqs <$> instGeneric 1 (determineFlavor Forall pos) βqs σ
instAll _ σ = return σ

-- | Instantiate an outer existential quantifier.
--   PRECONDITION: σ is fully substituted.
instEx ∷ MonadConstraint tv r m ⇒ Bool → Type tv → m (Type tv)
instEx pos (TyQu Exists αqs σ) = do
  traceN 4 ("instEx", pos, αqs, σ)
  instGeneric 0 (determineFlavor Exists pos) αqs σ
instEx _ σ = return σ

-- | Instantiate type variables and use them to open a type, given
--   a flavor and list of qualifier literal bounds.  Along with the
--   instantiated type, returns any new type variables.
--   PRECONDITION: σ is fully substituted.
instGeneric ∷ MonadConstraint tv r m ⇒
              Int → Flavor → [(a, QLit)] → Type tv →
              m (Type tv)
instGeneric k flav αqs σ = do
  αs ← zipWithM (newTV' <$$> (,flav,) . snd) αqs (inferKinds σ)
  return (openTy k (fvTy <$> αs) σ)

-- | What kind of type variable to create when instantiating
--   a given quantifier in a given polarity:
determineFlavor ∷ Quant → Bool → Flavor
determineFlavor Forall True  = Universal
determineFlavor Forall False = Skolem
determineFlavor Exists True  = Existential
determineFlavor Exists False = Universal

---
--- TYPE-MATCHING INSTANTIATION
---

-- | Given (maybe) a type, and a type constructor,
--   return a list of (maybe) parameter types and returns
--   a list of any new type variables.  The output types are @Nothing@
--   iff the input type is @Nothign@.  If the input type is a type
--   variable, it gets unified with the requested shape over fresh type
--   variables using the given type relation.
--   PRECONDITION: σ is fully substituted.
{-
Instantiates both ∀ and ∃ to univars:
  (λx.x) : A → A          ⇒       (λ(x:A). (x:A)) : A → A
  (λx.x) : ∀α. α → α      ⇒       (λ(x:β). (x:β)) : ∀α. α → α
  (λx.x) : ∀α. C α → C α  ⇒       (λ(x:C β). (x:C β)) : ∀α. C α → C α
  (λx.x) : ∃α. α → α      ⇒       (λ(x:β). (x:β)) : ∃α. α → α
  (λx.x) : ∃α. C α → C α  ⇒       (λ(x:C β). (x:C β)) : ∃α. C α → C α
-}
splitCon ∷ MonadConstraint tv r m ⇒
           -- | Type to split
           Maybe (Type tv) →
           -- | Expected type
           TyCon →
           m ([Maybe (Type tv)])
splitCon Nothing  tc = return (Nothing <$ tcArity tc)
splitCon (Just σ) tc = do
  traceN 4 ("splitCon", σ, tc)
  ρ ← instAllEx True False σ
  loop ρ
  where
  loop ρ = case ρ of
    TyApp tc' σs     | tc == tc'
      → return (Just <$> σs)
                     | Next ρ' ← headReduceType ρ
      → loop ρ'
    _ → return (Nothing <$ tcArity tc)

-- | Like 'splitCon', but for rows.
--   PRECONDITION: σ is fully substituted.
splitRow ∷ MonadConstraint tv r m ⇒
           -- | The type to split
           Maybe (Type tv) →
           -- | The row label that we're expecting
           RowLabel →
           m (Maybe (Type tv), Maybe (Type tv))
splitRow Nothing  _   = return (Nothing, Nothing)
splitRow (Just σ) lab = do
  traceN 4 ("splitRow", σ, lab)
  ρ ← instAllEx True False σ
  loop ρ
  where
  loop ρ = case ρ of
    TyRow lab' τ1 τ2 | lab' == lab
      → return (Just τ1, Just τ2)
                     | otherwise
      → do
        (mτ1, mτ2) ← loop τ2
        return (mτ1, TyRow lab' τ1 <$> mτ2)
    _ → return (Nothing, Nothing)

---
--- CONDITIONAL GENERALIZATION/INSTANTIATION
---

-- A system for specifying requested generalization/instantiation

-- | Used by 'infer' and helpers to specify a requested
--   generalization/instantiation state.
data Request tv
  = Request {
      -- | Request the type to have ∀ quantifiers generalized
      rqAll  ∷ !Bool,
      -- | Request the type to have ∃ quantifiers generalized
      rqEx   ∷ !Bool,
      -- | Require that the existential type variables among these
      --   be generalizable at the given ranks
      rqTVs  ∷ [(tv, Rank.Rank)],
      -- | Rank to which to generalize
      rqRank ∷ !Rank.Rank
    }

instance Ppr.Ppr tv ⇒ Ppr.Ppr (Request tv) where
  ppr φ = (if rqAll φ then Ppr.char '∀' else mempty)
          Ppr.<>
          (if rqEx φ then Ppr.char '∃' else mempty)
          Ppr.<>
          (if null (rqTVs φ)
             then mempty
             else Ppr.ppr (rqTVs φ) Ppr.<>
                  Ppr.char '/' Ppr.<> Ppr.ppr (rqRank φ))

-- | Defines a variadic function for building 'Request' states.  Minimal
--   definition: 'addToRequest'
class MkRequest r tv | r → tv where
  -- | Variadic function that constructs a 'Request' state given some
  --   number of parameters to modify it, as shown by instances below.
  request      ∷ r
  request      = addToRequest Request {
    rqAll   = False,
    rqEx    = False,
    rqTVs   = [],
    rqRank  = Rank.infinity
  }
  addToRequest ∷ Request tv → r

instance MkRequest (Request tv) tv where
  addToRequest = id

instance MkRequest r tv ⇒ MkRequest (Request tv → r) tv where
  addToRequest _ r' = addToRequest r'

instance (Tv tv, MkRequest r tv) ⇒ MkRequest (Γ tv' → [tv] → r) tv where
  addToRequest r γ αs = addToRequest r {
    rqTVs  = [(α, rank) | α ← αs, tvFlavorIs Existential α] ++ rqTVs r,
    rqRank = rank `min` rqRank r
  }
    where rank = rankΓ γ

instance MkRequest r tv ⇒ MkRequest (Rank.Rank → r) tv where
  addToRequest r rank = addToRequest r {
    rqRank = rank `min` rqRank r
  }

instance MkRequest r tv ⇒ MkRequest (Quant → r) tv where
  addToRequest r Forall = addToRequest r { rqAll = True }
  addToRequest r Exists = addToRequest r { rqEx = True }

-- 'maybeGen', 'maybeInst', and 'maybeInstGen' are the external
-- interface to conditional generalization.

-- | Generalize the requested flavors,·
maybeGen ∷ MonadConstraint tv r m ⇒
           AST.Expr R → Request tv → Γ tv → Type tv → m (Type tv)
maybeGen e0 φ γ σ = do
  let value = AST.syntacticValue e0
  traceN 4 ("maybeGen", value, φ, γ, σ)
  checkEscapingEx φ
  (if rqAll φ then generalize value (Rank.inc (rankΓ γ)) else return)
    >=>
    (if rqEx φ then generalizeEx (rankΓ γ `min` rqRank φ) else return)
    >=>
    (if rqAll φ then generalize value (rankΓ γ) else return)
    $ σ

maybeInstGen ∷ MonadConstraint tv r m ⇒
               AST.Expr R → Request tv → Γ tv → Type tv → m (Type tv)
maybeInstGen e φ γ σ = do
  σ' ← case () of
     _ | AST.isAnnotated e → return σ
       | rqAll φ           → return σ
       | rqEx φ            → instAll True =<< subst σ
       | otherwise         → instantiate σ
  maybeGen e φ γ σ'

-- | Check for escaping existential type variables
checkEscapingEx ∷ MonadConstraint tv r m ⇒ Request tv → m ()
checkEscapingEx φ = do
  αrs ← filterM escapes (rqTVs φ)
  tassert (null αrs) $
    case αrs of
      [(α,_)] → [msg| Existential type variable $α escapes its context. |]
      _       → [msg| Existential type variables escape their context: $ul:1 |]
                  [ pprMsg α | (α, _) ← αrs ]
  where
    escapes (α, rank) = (rank >=) <$> getTVRank α

---
--- INSTANTIATING ANNOTATION TYPE VARIABLES
---

-- | Given the environments, a piece of syntax, and a continuation,
--   call the continuation with the type variable environment extended
--   with fresh type variables for any annotation type variables in the
--   piece of syntax.
withTVsOf ∷ (MonadConstraint tv r m, HasAnnotations a R) ⇒
            Δ tv → Γ tv → a → (Δ tv → m b) → m b
withTVsOf δ γ stx kont = do
  let (αs, κs) = unzip (tvsWithKinds γ stx)
  αs' ← zipWithM (\α κ → newTV' (AST.tvqual α, κ)) αs κs
  kont (δ =+= αs =:*= αs')

-- | Given an expression, get its type variables with their kinds
tvsWithKinds ∷ HasAnnotations a R ⇒
               Γ tv → a → [(AST.TyVar R, Kind)]
tvsWithKinds γ = M.toList . annotFtvMap var con cmb where
  var _      = KdType
  con n ix = case γ =..= n of
    Just tc
      | variance:_ ← drop ix (tcArity tc)
      , isQVariance variance
      → \_ → KdQual
    _ → id
  cmb KdQual KdQual = KdQual
  cmb _      _      = KdType
