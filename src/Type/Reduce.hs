{-# LANGUAGE TypeFamilies #-}
module Type.Reduce (
  matchReduce,
  headNormalizeTypeK, headNormalizeType,
  headReduceType, ReductionState(..),
  majorReductionSequence, reductionSequence, reductionSequence'
) where

import Util
import Error
import Type.Internal
import Type.TyVar (Tv)
import Type.Ppr ()

import Prelude ()
import Data.Generics (Typeable, Data)
import qualified Data.List as List

instance Tv tv ⇒ Viewable (Type tv) where
  type View (Type tv) = Type tv
  view = headNormalizeTypeK 1000

-- | Reduce a type to head normal form
headNormalizeType ∷ Ord tv ⇒ Type tv → Type tv
headNormalizeType = last . reductionSequence

-- | Allow @k0@ steps to reduce a type to head normal form, or call
--  'error'
headNormalizeTypeK ∷ Tv tv ⇒ Int → Type tv → Type tv
headNormalizeTypeK k0 σ0 = loop k0 (reductionSequence σ0) where
  loop _ []     = throw $
    almsBug StaticsPhase "headNormalizeTypeK"
            "got empty reduction sequence"
  loop _ [σ]    = σ
  loop 0 (σ:_)  = throw $
    AlmsError StaticsPhase bogus
      [msg|
        Reduction of type $q:σ0 has not converged after $k0
        steps; stopped at $q:σ.
      |]
  loop k (_:σs) = loop (k - 1) σs

-- | Given two types, try to reduce them to a pair with a common
--   head constructor.
matchReduce ∷ Ord tv ⇒ Type tv → Type tv → Maybe (Type tv, Type tv)
matchReduce σ1 σ2 =
  List.find isCandidate
            (allPairsBFS (majorReductionSequence σ1)
                         (majorReductionSequence σ2))
  where
    isCandidate (TyApp tc _, TyApp tc' _) = tc == tc'
    isCandidate _                         = True

-- | Returns all pairs of a pair of lists, breadth first
allPairsBFS ∷ [a] → [b] → [(a, b)]
allPairsBFS xs0 ys0 = loop [(xs0, ys0)] where
  loop []   = []
  loop xsys = [ (x, y) | (x:_, y:_) ← xsys ]
           ++ loop (take 1 [ (xs, ys) | (xs, _:ys) ← xsys ]
                        ++ [ (xs, ys) | (_:xs, ys) ← xsys ])

-- | A major reduction sequence is a reduction sequence filtered
--   to show only changes in the head constructor.
majorReductionSequence ∷ Ord tv ⇒ Type tv → [Type tv]
majorReductionSequence = clean . reductionSequence where
  clean []        = []
  clean (TyApp tc _:σ:σs)
    | tc == tcRowMap
                  = clean (σ:σs)
  clean (σ:σs)    = σ : cleanWith σ σs
  cleanWith σ@(TyApp tc _) ((TyApp tc' _) : σs)
    | tc == tc'  = cleanWith σ σs
  cleanWith _ σs = clean σs

-- | The reduction sequence of a type
reductionSequence ∷ Ord tv ⇒ Type tv → [Type tv]
reductionSequence σ = (σ:) $ case headReduceType σ of
  Next σ' → reductionSequence σ'
  _       → []

-- | The reduction sequence of a type along with a final status
--   indicator
reductionSequence' ∷ Ord tv ⇒ Type tv → ([Type tv], ReductionState ())
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
headReduceType ∷ Ord tv ⇒ Type tv → ReductionState (Type tv)
headReduceType σ0 = case σ0 of
  TyQu _ _ _  → Done
  TyVar _     → Done
  TyRow _ _ _ → Done
  TyMu _ σ    → Next $ openTy 0 [σ0] σ
  TyApp tc [σ1, σ2] | tc == tcRowMap
              → applyRowMap σ1 σ2
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
  patt (TpRow _)      σ           = Right [σ]

applyRowMap ∷ Ord tv ⇒ Type tv → Type tv → ReductionState (Type tv)
applyRowMap σcxt σarg = case σarg of
  TyRow lab σ1 σ2
    → Next $ TyRow lab (plugHole σcxt σ1) (tyRowMap σcxt σ2)
  TyApp tc [] | tc == tcRowEnd
    → Next tyRowEnd
  _ → tyRowMap σcxt <$> headReduceType σarg

plugHole         ∷ Ord tv ⇒ Type tv → Type tv → Type tv
plugHole σcxt σ' = foldType (mkQuF TyQu) (mkBvF bvTy) fvTy fcon
                            TyRow (mkMuF TyMu) σcxt
  where
    fcon tc σs =
      if tc == tcRowHole
        then σ'
        else TyApp tc σs
