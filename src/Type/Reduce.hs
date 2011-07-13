{-# LANGUAGE
      DeriveDataTypeable,
      DeriveFunctor,
      QuasiQuotes,
      TypeFamilies,
      UnicodeSyntax
    #-}
module Type.Reduce (
  headNormalizeTypeK, headNormalizeType,
  headReduceType, ReductionState(..),
  reductionSequence, reductionSequence'
) where

import Util
import ErrorMessage
import Type.Internal
import Type.TyVar (Tv)
import Type.Syntax ()
import Data.Loc (bogus)

import Prelude ()
import Data.Generics (Typeable, Data)

instance Tv tv ⇒ Viewable (Type tv) where
  type View (Type tv) = Type tv
  view = headNormalizeTypeK 1000

-- | Reduce a type to head normal form
headNormalizeType ∷ Type tv → Type tv
headNormalizeType = last . reductionSequence

-- | Allow @k0@ steps to reduce a type to head normal form, or call
--  'error'
headNormalizeTypeK ∷ Tv tv ⇒ Int → Type tv → Type tv
headNormalizeTypeK k0 σ0 = loop k0 (reductionSequence σ0) where
  loop _ []     = throw $
    almsBug StaticsPhase bogus "headNormalizeTypeK"
            "got empty reduction sequence"
  loop _ [σ]    = σ
  loop 0 (σ:_)  = throw $
    AlmsException StaticsPhase bogus
      [msg|
        Reduction of type $q:σ0 has not converged after $k0
        steps; stopped at $q:σ.
      |]
  loop k (_:σs) = loop (k - 1) σs

-- | The reduction sequence of a type
reductionSequence ∷ Type tv → [Type tv]
reductionSequence σ = (σ:) $ case headReduceType σ of
  Next σ' → reductionSequence σ'
  _       → []

-- | The reduction sequence of a type along with a final status
--   indicator
reductionSequence' ∷ Type tv → ([Type tv], ReductionState ())
reductionSequence' σ = first (σ:) $ case headReduceType σ of
  Next σ' → reductionSequence' σ'
  rs      → ([], () <$ rs)

-- | The state of a type reduction
data ReductionState t
  -- | The type is head-normal -- that is, its head constructor is
  --   not a type synonym/operator
  = Done
  -- | The type has a next head-reduction step
  | Next t
  -- | The type may reduce further in the future, but right now it
  --   has a pattern match that depends on the value of a type variable
  | Blocked
  -- | The type's head constructor is a synonym/operator, but it
  --   can never take a step, due to a failed pattern match
  | Stuck
  deriving (Eq, Ord, Show, Functor, Typeable, Data)

-- | Perform one head reduction step.
headReduceType ∷ Type tv → ReductionState (Type tv)
headReduceType σ0 = case σ0 of
  TyQu _ _ _  → Done
  TyVar _     → Done
  TyRow _ _ _ → Done
  TyMu _ σ    → Next $ openTy 0 [σ0] σ
  TyApp tc σs → maybe Done (clauses tc σs) (tcNext tc)
  where
  --
  clauses _  _  []                = Stuck
  clauses tc σs ((tps, rhs):rest) = case patts tps σs of
    Right σs'  → Next $ openTy 0 σs' (elimEmptyF rhs)
    Left Stuck → clauses tc σs rest
    Left rs    → TyApp tc <$> rs
  --
  patts []       []               = Right []
  patts (tp:tps) (σ:σs)           = case patt tp σ of
    Right σs'     → case patts tps σs of
      Right σss'      → Right (σs' ++ σss')
      Left rs         → Left ((σ:) <$> rs)
    Left Blocked  → Left $ either ((σ:) <$>) (const Blocked) (patts tps σs)
    Left rs       → Left $ (:σs) <$> rs
  patts _        _                = Left Stuck
  --
  patt (TpVar _)       σ          = Right [σ]
  patt (TpApp tc tps)  σ          = case σ of
    TyApp tc' σs
      | tc == tc' → ((TyApp tc' <$>) +++ id) (patts tps σs)
    TyVar _       → Left Blocked
    _             → case headReduceType σ of
      Done            → Left Stuck
      rs              → Left rs
  patt (TpRow _)      _           = throw $
    almsBug StaticsPhase bogus "headReduceType"
      "Row patterns are not yet implemented."
