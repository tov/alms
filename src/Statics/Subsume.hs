-- | Subsumption
module Statics.Subsume (
  subsumeN, (≤), (≤≥), subsumeBy,
) where

import Util
import Statics.Constraint
import Statics.Error
import Statics.InstGen
import Type

import Prelude ()
import qualified Data.Set as S

-- | Given a list of type/U-action pairs, run all the U actions, but
--   in an order that does all U-actions not assocated with tyvars
--   before those associated with tyvars. Checks dynamically after each
--   action, since an action can turn a tyvar into a non-tyvar.
subsumeN ∷ MonadConstraint tv r m ⇒
           [(Type tv, m ())] → m ()
subsumeN []  = return ()
subsumeN σs0 = subsumeOneOf σs0 >>= subsumeN
  where
    subsumeOneOf []             = return []
    subsumeOneOf [(_, u1)]      = [] <$ u1
    subsumeOneOf ((σ1, u1):σs)  = do
      σ ← substHead σ1
      case σ of
        TyVar (Free α) | tvFlavorIs Universal α
          → ((σ, u1):) <$> subsumeOneOf σs
        _ → σs <$ u1

-- | Subsumption
(≤)   ∷ MonadConstraint tv r m ⇒ Type tv → Type tv → m ()
σ1 ≤ σ2 = do
  traceN 2 ("≤", σ1, σ2)
  subsumeBy (<:) σ1 σ2

-- | Subsumption
(≤≥)  ∷ MonadConstraint tv r m ⇒ Type tv → Type tv → m ()
σ1 ≤≥ σ2 = do
  traceN 2 ("≤≥", σ1, σ2)
  subsumeBy (=:) σ1 σ2

subsumeBy ∷ MonadConstraint tv r m ⇒
            (Type tv → Type tv → m ()) → Type tv → Type tv → m ()
subsumeBy (≤*) σ10 σ20 = do
  σ1 ← subst σ10
  σ2 ← subst σ20
  case (σ1, σ2) of
    (TyVar (Free α), _) | tvFlavorIs Universal α → do
      σ1 ≤* σ2
    (_, TyVar (Free α)) | tvFlavorIs Universal α → do
      σ1' ← instAll True σ1
      σ1' ≤* σ2
    _ → do
      ρ1        ← instantiate σ1
      (ρ2, αs2) ← collectTVs (instantiateNeg σ2)
      ρ1 ≤* ρ2
      -- Check for escaping skolems
      let (us1, _, ss1) = partitionFlavors αs2
      σ1'  ← subst σ1
      σ2'  ← subst σ2
      us1' ← mapM subst (fvTy <$> us1)
      let freeSkolems = S.filter (tvFlavorIs Skolem) (ftvSet (σ1', σ2', us1'))
      when (any (`S.member` freeSkolems) ss1) $ do
        traceN 3 (αs2, freeSkolems)
        tErrExp
          [msg|
            Cannot subsume types because a type is less
            polymorphic than expected:
          |]
          (pprMsg σ1')
          (pprMsg σ2')

-- | Given a list of type variables, partition it into a triple of lists
--   of 'Universal', 'Existential', and 'Skolem' flavored type variables.
partitionFlavors ∷ Tv tv ⇒
                   [tv] → ([tv], [tv], [tv])
partitionFlavors = loop [] [] [] where
  loop us es ss []     = (us, es, ss)
  loop us es ss (α:αs) = case tvFlavor α of
    Universal   → loop (α:us) es     ss     αs
    Existential → loop us     (α:es) ss     αs
    Skolem      → loop us     es     (α:ss) αs

