{-# LANGUAGE
      FlexibleContexts,
      FlexibleInstances,
      FunctionalDependencies,
      MultiParamTypeClasses,
      ParallelListComp,
      QuasiQuotes,
      ScopedTypeVariables,
      TemplateHaskell,
      TupleSections,
      UndecidableInstances,
      UnicodeSyntax
    #-}
module Statics.Expr {-(
  tcExpr
)-} where

import Util
import qualified AST
import qualified AST.Patt
import AST.TypeAnnotation
import Meta.Quasi
import qualified Rank
import Type
import qualified Syntax.Ppr as Ppr
import Statics.Env
import Statics.Error
import Statics.Constraint
import Statics.Type

import Prelude ()
import qualified Data.Map as M
import qualified Data.Set as S

tcExpr ∷ MonadConstraint tv r m ⇒
         Δ tv → Γ tv → AST.Expr R → m (AST.Expr R, Type tv)
tcExpr δ γ e = withTVsOf δ γ e $ \δ' → do
  infer δ' γ e Nothing

infer  ∷ MonadConstraint tv r m ⇒
         Δ tv → Γ tv → AST.Expr R → Maybe (Type tv) →
         m (AST.Expr R, Type tv)
infer δ γ e0 mσ0 = undefined

---
--- MISCELLANEOUS HELPERS
---

-- | Determine which quantifiers may appear at the beginning of
--   a type scheme, given a list of quantifiers that may be presumed
--   to belong to an unsubstituted variable.
prenexFlavors ∷ Type tv → Request tv' → Request tv'
prenexFlavors σ φ =
  case σ of
    TyQu Exists _ (TyQu Forall _ _) → φ { rqEx = True, rqAll = True }
    TyQu Exists _ (TyVar _)         → φ { rqEx = True }
    TyQu Exists _ _                 → φ { rqEx = True, rqAll = False }
    TyQu Forall _ _                 → φ { rqEx = False, rqAll = True }
    TyVar _                         → φ
    _                               → φ { rqEx = False, rqAll = False }

-- | To compute the qualifier expression for a function type.
arrowQualifier ∷ Ord tv ⇒ Γ tv → AST.Expr R → QExpV tv
arrowQualifier γ e =
  bigJoin [ qualifier (γ =..= n)
          | n      ← M.keys (AST.fv e) ]

-- | Extract and instantiate the annotations in a pattern as an annotation.
extractPattAnnot ∷ MonadConstraint tv r m ⇒
                   Δ tv → Γ tv → AST.Patt R → m (Maybe (Type tv))
extractPattAnnot δ γ = loop where
  loop [pa| _ |]                = return Nothing
  loop [pa| $vid:_ |]           = return Nothing
  loop [pa| $qcid:_ $opt:_ |]   = return Nothing
  loop [pa| ($π1, $π2) |]       = do
    mσ1 ← loop π1
    mσ2 ← loop π2
    case (mσ1, mσ2) of
      (Just σ1, Just σ2)   → return (Just (tyTuple σ1 σ2))
      (Just σ1, Nothing)   → Just . tyTuple σ1 <$> newTVTy
      (Nothing, Just σ2)   → Just . flip tyTuple σ2 <$> newTVTy
      (Nothing, Nothing)   → return Nothing
  loop [pa| $lit:_ |]           = return Nothing
  loop [pa| $π as $vid:_ |]     = loop π
  loop [pa| `$uid:_ |]          = return Nothing
  loop [pa| `$uid:uid $π |]     = do
    mσ ← loop π
    case mσ of
      Just σ  → Just . TyRow uid σ <$> newTVTy
      Nothing → return Nothing
  loop [pa| $_ : $annot |]      = Just <$> tcType δ γ annot
  loop [pa| ! $π |]             = loop π
  loop [pa| $anti:a |]          = $(AST.antierror)

-- | Extend the environment and update the ranks of the free type
--   variables of the added types.
(!+!) ∷ MonadSubst tv r m ⇒ Γ tv → Γv tv → m (Γ tv)
γ !+! γv = do
  lowerRank (Rank.inc (rankΓ γ)) (range γv)
  return (bumpΓ γ =+= γv)
infixl 2 !+!

---
--- SUBSUMPTION OPERATIONS
---

-- | Given a list of type/U-action pairs, run all the U actions, but
--   in an order that does all U-actions not assocated with tyvars
--   before those associated with tyvars. Checks dynamically after each
--   action, since an action can turn a tyvar into a non-tyvar.
subsumeN ∷ MonadConstraint tv r m ⇒
           [(Type tv, m ())] → m ()
subsumeN [] = return ()
subsumeN σs = subsumeOneOf σs >>= subsumeN
  where
    subsumeOneOf []             = return []
    subsumeOneOf [(_, u1)]      = [] <$ u1
    subsumeOneOf ((σ1, u1):σs)  = do
      σ ← substHead σ1
      case σ of
        TyVar (Free α) | tvFlavorIs Universal α
          → ((σ, u1):) <$> subsumeOneOf σs
        _ → σs <$ u1

-- | Given a function arity and a type, extracts a list of argument
--   types and a result type of at most the given arity.
funmatchN ∷ MonadConstraint tv r m ⇒
            Int → Type tv → m ([Type tv], Type tv)
funmatchN n0 σ0 = loop n0 =<< subst σ0
  where
  loop 0 σ = return ([], σ)
  loop n σ = case σ of
    TyApp tc [σ1, _, σ']        | tc == tcFun
      → first (σ1:) <$> loop (n - 1) σ'
    TyApp _ _                   | Next σ' ← headReduceType σ
      → loop n σ'
    TyVar (Free α)              | tvFlavorIs Universal α
      → do
      β1 ← newTVTy
      qe ← qvarexp . Free <$> newTV' KdQual
      β2 ← newTVTy
      σ =: tyFun qe β1 β2
      return ([β1], β2)
    TyMu _ σ1
      → loop n (openTy 0 [σ] σ1)
    _ → do
      tErrExp_
        [msg| In application expression, operator is not a function: |]
        [msg| $σ |]
        [msg| a function type |]
      βs ← replicateM n newTVTy
      β2 ← newTVTy
      return (βs, β2)

-- | Subsumption
(≤)   ∷ MonadConstraint tv r m ⇒ Type tv → Type tv → m ()
σ1 ≤ σ2 = do
  traceN 2 ("≤", σ1, σ2)
  subsumeBy (<:) σ1 σ2

subsumeBy ∷ MonadConstraint tv r m ⇒
            (Type tv → Type tv → m ()) → Type tv → Type tv → m ()
subsumeBy (<*) σ1 σ2 = do
  σ1' ← subst σ1
  σ2' ← subst σ2
  case (σ1', σ2') of
    (TyVar (Free α), _) | tvFlavorIs Universal α → do
      σ1' <* σ2'
    (_, TyVar (Free α)) | tvFlavorIs Universal α → do
      σ1' ← instAll True σ1'
      σ1' <* σ2'
    _ → do
      ρ1        ← instantiate σ1'
      (ρ2, αs2) ← collectTVs (instantiateNeg σ2')
      ρ1 <* ρ2
      -- Check for escaping skolems
      let (us1, _, ss1) = partitionFlavors αs2
      σ1'' ← subst σ1'
      σ2'' ← subst σ2'
      us1' ← mapM subst (fvTy <$> us1)
      let freeSkolems = S.filter (tvFlavorIs Skolem) (ftvSet (σ1'', σ2'', us1'))
      when (any (`S.member` freeSkolems) ss1) $ do
        traceN 3 (αs2, freeSkolems)
        tErrExp
          [msg|
            Cannot subsume types because a type is less
            polymorphic than expected:
          |]
          (pprMsg σ1'')
          (pprMsg σ2'')

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

-- | Given a type relation, (maybe) a type, and a type constructor,
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
           -- | Who's asking?
           String →
           -- | Unifier for type variables forced to a shape
           (Type tv → Type tv → m ()) →
           -- | Type to split
           Maybe (Type tv) →
           -- | Expected type
           TyCon →
           m ([Maybe (Type tv)])
splitCon _   _    Nothing  tc = return (Nothing <$ tcArity tc)
splitCon who (<*) (Just σ) tc = do
  traceN 4 ("splitCon", who, σ, tc)
  ρ ← instAllEx True False σ
  loop ρ
  where
  loop ρ = case ρ of
    TyApp tc' σs     | tc == tc'
      → return (Just <$> σs)
                     | Next ρ' ← headReduceType ρ
      → loop ρ'
    TyVar (Free α)   | tvFlavorIs Universal α
      → do
          αs ← replicateM (length (tcArity tc)) (newTVTy' (tvDescr α))
          ρ <* TyApp tc αs
          return (Just <$> αs)
    _ → tErrExp
          [msg| Unexpected type in $<who>: |]
          [msg| $σ |]
          (pprMsg (TpApp tc (TpVar Nope <$ tcArity tc)))

-- | Like 'splitCon', but for rows.
--   PRECONDITION: σ is fully substituted.
splitRow ∷ MonadConstraint tv r m ⇒
           -- | Who is asking?
           String →
           -- | Coercion to unify type variable with required shape
           (Type tv → Type tv → m ()) →
           -- | The type to split
           Maybe (Type tv) →
           -- | The row label that we're expecting
           RowLabel →
           m (Maybe (Type tv), Maybe (Type tv))
splitRow _   _    Nothing  _    = return (Nothing, Nothing)
splitRow who (<*) (Just σ) lab = do
  traceN 4 ("splitRow", who, σ, lab)
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
    TyVar (Free α)   | tvFlavorIs Universal α
      → do
          τ1 ← newTVTy
          τ2 ← newTVTy
          ρ <* TyRow lab τ1 τ2
          return (Just τ1, Just τ2)
    TyApp _ _        | Next ρ' ← headReduceType ρ
      → loop ρ'
    _ → tErrExp
          [msg| Unexpected type in $<who>: |]
          [msg| $σ |]
          [msg| a value constructed with `$lab |]

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
  σ ← if rqAll φ
        then generalize value (Rank.inc (rankΓ γ)) σ
        else return σ
  σ ← if rqEx φ
        then generalizeEx (rankΓ γ `min` rqRank φ) σ
        else return σ
  if rqAll φ
        then generalize value (rankΓ γ) σ
        else return σ

maybeInstGen ∷ MonadConstraint tv r m ⇒
               AST.Expr R → Request tv → Γ tv → Type tv → m (Type tv)
maybeInstGen e φ γ σ = do
  σ ← case () of
    _ | AST.isAnnotated e → return σ
      | rqAll φ           → return σ
      | rqEx φ            → instAll True =<< subst σ
      | otherwise         → instantiate σ
  maybeGen e φ γ σ

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
  αs' ← mapM newTV' κs
  kont (δ =+= αs =:*= αs')

-- | Given an expression, get its type variables with their kinds
tvsWithKinds ∷ HasAnnotations a R ⇒
               Γ tv → a → [(AST.TyVar R, Kind)]
tvsWithKinds γ = M.toList . (unKindLat <$$> annotFtvMap var con) where
  var _      = KindLat KdType
  con n ix = case γ =..= n of
    Just tc
      | variance:_ ← drop ix (tcArity tc)
      , isQVariance variance
      → \_ → KindLat KdQual
    _ → id

newtype KindLat = KindLat { unKindLat ∷ Kind }

instance Monoid KindLat where
  mempty = KindLat KdQual
  mappend (KindLat KdQual) (KindLat KdQual) = KindLat KdQual
  mappend _                _                = KindLat KdType

