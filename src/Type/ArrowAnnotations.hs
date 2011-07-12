{-# LANGUAGE
      CPP,
      QuasiQuotes,
      TemplateHaskell,
      UnicodeSyntax
    #-}
-- | Rules for interpreting arrow qualifier annotations.
module Type.ArrowAnnotations (
  -- * Between internal and external qualifier expressions
  qInterpret, qRepresent,
  -- * Arrow annotation rules
  ImpArrRule(..), CurrentImpArrRule, CurrentImpArrPrintingRule,
) where

import Util
import Meta.Quasi
import qualified Syntax.Notable
import qualified Syntax
import Type.Internal

import Prelude ()
import qualified Data.Set as S

-- | The rule for parsing arrows
#ifdef ANNOTATION_RULE
type CurrentImpArrRule = ANNOTATION_RULE
#else
type CurrentImpArrRule = Rule4
#endif

-- | The rule for printing arrows
#ifdef ANNOTATION_PRINTING_RULE
type CurrentImpArrPrintingRule = ANNOTATION_PRINTING_RULE
#else
type CurrentImpArrPrintingRule = CurrentImpArrRule
#endif

-- | Interpret an explicit external qualifier as an internal one
qInterpret ∷ (Ord tv, Monad m) ⇒
             (Syntax.TyVar R → m (TyVar tv)) →
             Syntax.QExp R → m (QExpV tv)
qInterpret resolve = loop where
  loop [qeQ| $qlit:ql |]    = return (qlitexp ql)
  loop [qeQ| `$tv |]        = qvarexp `liftM` resolve tv
  loop [qeQ| $qe1 ⋁ $qe2 |] = (⊔) `liftM` loop qe1 `ap` loop qe2
  loop [qeQ| $anti:a |]     = $(Syntax.antifail)

-- | Represent an internal qualifier as an explicit external one
qRepresent ∷ (TyVar tv → Syntax.TyVar R) →
             QExpV tv → Syntax.QExp R
qRepresent _      QeA       = [qeQ|+! A |]
qRepresent rename (QeU tvs)
  | S.null tvs              = [qeQ|+! U |]
  | otherwise               =
      foldr1 Syntax.qeJoin (Syntax.qeVar . rename <$> S.toList tvs)

-- | Interface to rules for implicit annotation of arrows
class ImpArrRule rule where
  -- | The initial labeling state
  iaeInit      ∷ rule tv
  -- | Update the state to the left of an arrow
  iaeLeft      ∷ rule tv → rule tv
  -- | Update the state to the right of an arrow with the given
  --   qualifier
  iaeRight     ∷ Ord tv ⇒ rule tv → QExpV tv → Type tv → rule tv
  -- | The implied qualifier at a particular point
  iaeImplied   ∷ rule tv → QExpV tv
  -- | Interpret the given implicit qualifier into an explicit qualifier
  --   at the given point
  iaeInterpret ∷ (Ord tv, Monad m) ⇒
                 (Syntax.TyVar R → m (TyVar tv)) →
                 rule tv → Maybe (Syntax.QExp R) → m (QExpV tv)
  -- | Represent the given explicit qualifier as an implicit one
  iaeRepresent ∷ Eq tv ⇒
                 (TyVar tv → Syntax.TyVar R) →
                 rule tv → QExpV tv → Maybe (Syntax.QExp R)
  -- | Update the state under the given variance
  iaeUnder     ∷ rule tv → Variance → rule tv
  --
  iaeLeft _           = iaeInit
  iaeRight iae _ _    = iae
  iaeImplied _        = minBound
  iaeInterpret resolve iae
                      = maybe (return (iaeImplied iae)) (qInterpret resolve)
  iaeRepresent rename iae actual
    | actual == iaeImplied iae = Nothing
    | otherwise                = Just (qRepresent rename actual)
  iaeUnder _ _        = iaeInit

-- | Print all arrow annotations explicitly
data Rule0 tv = Rule0

instance ImpArrRule Rule0 where
  iaeInit                       = Rule0
  iaeRepresent rename _ actual  = Just (qRepresent rename actual)

-- | Annotation ‘U’ is implicit for unlabeled arrows.
data Rule1 tv = Rule1

instance ImpArrRule Rule1 where
  iaeInit        = Rule1

newtype Rule2 tv = Rule2 { unRule2 ∷ QExpV tv }

-- | Implicit annotation is lub of qualifiers of prior curried
--   arguments.  Explicit annotations have no effect on subsequent
--   arrows.
instance ImpArrRule Rule2 where
  iaeInit          = Rule2 minBound
  iaeRight iae _ t = Rule2 (unRule2 iae ⊔ qualifier t)
  iaeImplied       = unRule2

-- | Like 'Rule2', but explicit annotations reset the qualifier to
--   themselves for subsequent arrows.
newtype Rule3 tv = Rule3 { unRule3 ∷ QExpV tv }

instance ImpArrRule Rule3 where
  iaeInit      = Rule3 minBound
  iaeRight iae actual t
    | unRule3 iae == actual = Rule3 (unRule3 iae ⊔ qualifier t)
    | otherwise             = Rule3 (actual ⊔ qualifier t)
  iaeImplied   = unRule3

-- | Like 'Rule3', but we arrow the implicit qualifer into covariant
--   type constructors.
newtype Rule4 tv = Rule4 { unRule4 ∷ QExpV tv }

instance ImpArrRule Rule4 where
  iaeInit      = Rule4 minBound
  iaeRight iae actual t
    | unRule4 iae == actual = Rule4 (unRule4 iae ⊔ qualifier t)
    | otherwise             = Rule4 (actual ⊔ qualifier t)
  iaeImplied   = unRule4
  iaeUnder iae Covariant    = iae
  iaeUnder _   _            = iaeInit

-- | Like 'Rule4', but we carry the implicit quantifier into ALL type
--   constructors and only use it when we arrive at an arrow in a
--   positive position wrt the surrounding arrow.
data Rule5 tv
  = Rule5 {
      unRule5 ∷ !(QExpV tv),
      r4Var   ∷ !Variance
    }

instance ImpArrRule Rule5 where
  iaeInit      = Rule5 minBound 1
  iaeRight iae actual t
    | unRule5 iae == actual = Rule5 (unRule5 iae ⊔ qualifier t) 1
    | otherwise             = Rule5 (actual ⊔ qualifier t) 1
  iaeImplied iae
    | r4Var iae == 1 = unRule5 iae
    | otherwise      = minBound
  iaeUnder iae var          = Rule5 (unRule5 iae) (var * r4Var iae)
