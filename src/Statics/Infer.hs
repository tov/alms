{-#
  LANGUAGE
    FlexibleContexts,
    FlexibleInstances,
    FunctionalDependencies,
    ImplicitParams,
    MultiParamTypeClasses,
    NoImplicitPrelude,
    ParallelListComp,
    ScopedTypeVariables,
    TupleSections,
    UndecidableInstances,
    UnicodeSyntax
  #-}
module Infer {-(
  inferTm, infer,
  -- * Testing
  -- ** Interactive testing
  check, showInfer,
  -- ** Unit tests
  inferTests, tests,
)-} where

{-
import qualified Data.Map   as Map
import qualified Data.Set   as Set
import qualified Test.HUnit as T

import Data.Time.Clock.POSIX (POSIXTime, getPOSIXTime)
import System.IO (stderr, hPutStrLn)
import System.Timeout (timeout)
import qualified Text.PrettyPrint as Ppr

import Constraint
import Env
import qualified Rank
import Syntax hiding (tests)
import TV
import Ppr
import Util

---
--- Inference
---

-- | Infer the type of a term, given a type context
inferTm ∷ (MonadTV tv r m, Show tv, Tv tv) ⇒
          Γ tv → Term Empty → m (Type tv, String)
inferTm γ e = do
  traceN 2 ("inferTm", γ, e)
  runConstraintT $ do
    δ ← instAnnotTVs (ftvPure e)
    τ ← infer (request AllQu ExQu) δ γ e Nothing
    σ ← generalize False (rankΓ γ) τ
    c ← showConstraint
    return (σ, c)

---
--- Type inference for terms and patterns, including matching and
--- application terms
---

-- | To infer the type of a term.
infer ∷ MonadC tv r m ⇒
        -- | Which quantifiers are requested on the resulting type, which
        --   may result in generalization or instantiation.
        Request tv →
        -- | The type annotation environment mapping names of some-bound
        --   type variables to unification variables.
        Δ tv →
        -- | The type environment mapping term variables to types.
        Γ tv →
        -- | The term to type.
        Term Empty →
        -- | Maybe the expected result type, used for annotation
        --   propagation.
        Maybe (Type tv) →
        m (Type tv)
infer φ0 δ γ e0 mσ0 = do
  traceN 1 (TraceIn ("infer", φ0, γ, e0, mσ0))
  mσ ← mapM substDeep mσ0
  let φ = maybe id prenexFlavors mσ φ0
  σ  ← case e0 of
    AbsTm π e                     → do
      [mσ1,_,mσ2]      ← splitCon (<:) mσ "->" 3
      ((σ1, σs), αs) ← collectTV $
        inferPatt δ π mσ1 (countOccsPatt π e)
      αs'              ← filterM (isMonoType . fst) ((fvTy &&& tvDescr) <$> αs)
      γ'               ← γ &+&! π &:& σs
      σ2               ← infer (request ExQu γ αs) δ γ' e mσ2
      qe               ← arrowQualifier γ (AbsTm π e)
      sequence_
        [ unlessM (isMonoType α) $
            fail $ "Type error: Used " ++ descr ++ " polymorphically"
        | (α, descr) ← αs' ]
      maybeGen e0 φ γ (arrTy σ1 qe σ2)
    LetTm π e1 e2                 → do
      mσ1              ← extractPattAnnot δ π
      ((_, σs), αs)    ← collectTV $ do
        σ1               ← infer (request AllQu ExQu) δ γ e1 mσ1
        inferPatt δ π (Just σ1) (countOccsPatt π e2)
      γ'               ← γ &+&! π &:& σs
      infer (request φ γ αs) δ γ' e2 mσ
    MatTm e1 bs                   → do
      (σ1, αs)         ← collectTV (infer request δ γ e1 Nothing)
      inferMatch (request φ γ αs) δ γ σ1 bs mσ
    RecTm bs e2                   → do
      let (ns, es) = unzip bs
          mas      = getTermAnnot <$> es
      σs           ← mapM (maybe newTVTy (instAnnot δ)) mas
      γ'           ← γ &+&! ns &:& σs
      σs'          ← sequence
        [ do
            unless (syntacticValue ei) $
              fail $ "In let rec, binding for ‘" ++ ni ++
                     "’ is not a syntactic value"
            σi ⊏: U
            infer request δ γ' ei (σi <$ mai)
        | (ni, ei) ← bs
        | mai      ← mas
        | σi       ← σs ]
      zipWithM (<:) σs' σs
      σs''             ← generalizeList True (rankΓ γ) σs'
      γ'               ← γ &+&! ns &:& σs''
      infer φ δ γ' e2 mσ
    VarTm n                       → maybeInstGen e0 φ γ =<< γ &.& n
    ConTm n es                    → do
      mσs              ← splitCon (flip (<:)) mσ n (length es)
      ρs               ← zipWithM (infer request δ γ) es mσs
      maybeGen e0 φ γ (ConTy n ρs)
    LabTm b n                     → do
      instantiate . elimEmptyF . read $
        "∀α r. " ++ (if b then 'α' else 'r') : " → [ " ++ n ++ " : α | r ]"
    AppTm _ _                     → do
      let (e, es) = unfoldApp e0
      (σ, αs)          ← collectTV $ do
        σ1               ← infer request δ γ e Nothing
        inferApp δ γ σ1 es
      maybeInstGen e0 (request φ γ αs) γ σ
    AnnTm e annot                 → do
      -- infer φ δ γ (AppTm (AbsTm (AnnPa (VarPa "x") annot) (VarTm "x")) e) mσ
      σ                ← instAnnot δ annot
      αs               ← collectTV_ . withPinnedTVs σ $ do
        σ'               ← infer request δ γ e (Just σ)
        σ' ≤ σ
      maybeGen e0 (request φ γ αs) γ σ
  traceN 1 (TraceOut ("infer", σ))
  return σ

-- | To infer a type of a match form, including refinement when matching
--   open variants.
inferMatch ∷ MonadC tv r m ⇒
             Request tv → Δ tv → Γ tv → Type tv →
             [(Patt Empty, Term Empty)] → Maybe (Type tv) → 
             m (Type tv)
inferMatch _ _ _ _ [] _ = newTVTy
inferMatch φ δ γ σ ((InjPa n πi, ei):bs) mσ | totalPatt πi = do
  β               ← newTVTy
  mσ12            ← extractLabel n <$> substDeep σ
  (σ1, σ2)        ← case mσ12 of
    Just σ12 → return σ12
    Nothing  → do
      σ1 ← newTVTy
      σ2 ← newTVTy
      σ =: RowTy n σ1 σ2
      return (σ1, σ2)
  ((_, σs), αs)   ← collectTV $ inferPatt δ πi (Just σ1) (countOccsPatt πi ei)
  γ'              ← γ &+&! πi &:& σs
  σi              ← infer (request φ γ αs) δ γ' ei mσ
  σk              ← if null bs
                      then do σ2 <: endTy; return β
                      else inferMatch φ δ γ σ2 bs mσ
  mapM_ (σ ⊏:) (countOccsPatt πi ei)
  if (isAnnotated ei)
    then σi <: β
    else σi ≤  β
  σk <: β
  return β
inferMatch φ δ γ σ ((πi, ei):bs) mσ = do
  β               ← newTVTy
  ((_, σs), αs)   ← collectTV $ inferPatt δ πi (Just σ) (countOccsPatt πi ei)
  γ'              ← γ &+&! πi &:& σs
  σi              ← infer (request φ γ αs) δ γ' ei mσ
  σk              ← inferMatch φ δ γ σ bs mσ
  if (isAnnotated ei)
    then σi <: β
    else σi ≤  β
  σk <: β
  return β

-- | Given a type variable environment, a pattern, maybe a type to
--   match, and a list of how each bound variable will be used,
--   and compute an updated type variable environment,
--   a type for the whole pattern, a type for each variable bound by
--   the pattern, and a list of some-quantified type variables.
--   PRECONDITION: mσ0 is fully substituted
inferPatt ∷ MonadC tv r m ⇒
            Δ tv → Patt Empty → Maybe (Type tv) → [Occurrence] →
            m (Type tv, [Type tv])
inferPatt δ π0 mσ0 occs = do
  traceN 1 (TraceIn ("inferPatt", δ, π0, mσ0, occs))
  (σ, σs) ← runWriterT (loop π0 mσ0)
  zipWithM_ (⊏:) σs occs
  traceN 1 (TraceOut ("inferPatt", σ, σs))
  return (σ, σs)
  where
  loop (VarPa n)       mσ = do
    σ ← maybeFresh mσ $ "unannotated parameter ‘" ++ n ++ "’"
    bind σ
    return σ
  loop WldPa           mσ = do
    σ ← maybeFresh mσ $ "unannotated wildcard pattern"
    return σ
  loop (ConPa name πs) mσ = do
    mαs ← splitCon (<:) mσ name (length πs)
    σs  ← zipWithM loop πs mαs
    mσ ?≤ ConTy name σs
  loop (InjPa name π)  mσ = do
    (mα, mβ) ← splitRow (<:) mσ name
    σ1 ← loop π mα
    σ2 ← maybeFresh mβ $ ""
    mσ ?≤ RowTy name σ1 σ2
  loop (AnnPa π annot) mσ = do
    σ' ← instAnnot δ annot
    σ  ← mσ ?≤ σ'
    loop π (Just σ')
    return σ
  --
  bind τ         = tell [τ]
  maybeFresh mσ doc = case mσ of
    Nothing → newTVTy' doc
    Just σ  → do
      σ' ← substRoot σ
      case σ' of
        VarTy (FreeVar α) → reportTV α
        _ → return ()
      return σ'
  --
  Nothing ?≤ σ' = return σ'
  Just σ  ?≤ σ' = do σ ≤ σ'; return σ

inferApp ∷ MonadC tv r m ⇒
           Δ tv → Γ tv → Type tv → [Term Empty] → m (Type tv)
inferApp δ γ ρ e1n = do
  traceN 2 (TraceIn ("inferApp", γ, ρ, e1n))
  (σ1m, σ) ← funmatchN (length e1n) ρ
  withPinnedTVs ρ $
    subsumeN [ -- last arg to infer (Just σi) is for
               -- formal-to-actual propagation
               (σi, do
                      σi' ← infer (request ExQu) δ γ ei (Just σi)
                      traceN 2 ("subsumeI", i, ei, σi', σi)
                      if isAnnotated ei
                        then σi' <: σi
                        else σi' ≤  σi)
             | i  ← [0 ∷ Int ..]
             | σi ← σ1m
             | ei ← e1n ]
  if length σ1m < length e1n
    then do
      ρ' ← instantiate σ
      inferApp δ γ ρ' (drop (length σ1m) e1n)
    else do
      traceN 2 (TraceOut ("inferApp", σ))
      return σ

--
-- Inference helpers
--

-- | Determine which quantifiers may appear at the beginning of
--   a type scheme, given a list of quantifiers that may be presumed
--   to belong to an unsubstituted variable.
prenexFlavors ∷ Type tv → Request tv' → Request tv'
prenexFlavors σ φ =
  case σ of
    QuaTy ExQu _ (QuaTy AllQu _ _) → φ { rqEx = True, rqAll = True }
    QuaTy ExQu _ (VarTy _)         → φ { rqEx = True }
    QuaTy ExQu _ _                 → φ { rqEx = True, rqAll = False }
    QuaTy AllQu _ _                → φ { rqEx = False, rqAll = True }
    VarTy _                        → φ
    _                              → φ { rqEx = False, rqAll = False }

-- | To compute the qualifier expression for a function type.
arrowQualifier ∷ MonadTV tv r m ⇒ Γ tv → Term a → m (QExp tv)
arrowQualifier γ e =
  qualifier (ConTy "U" [ σ
                       | n ← Set.toList (termFv e)
                       , σ ← γ &.& n ])

-- | To extend the environment and update the ranks of the free type
--   variables of the added types.
(&+&!) ∷ MonadTV tv r m ⇒ Γ tv → Map.Map Name (Type tv) → m (Γ tv)
γ &+&! m = do
  lowerRank (Rank.inc (rankΓ γ)) (Map.elems m)
  return (bumpΓ γ &+& m)
infixl 2 &+&!

-- | Extract the annotations in a pattern as an annotation.
extractPattAnnot ∷ MonadTV tv r m ⇒
                   Δ tv → Patt Empty → m (Maybe (Type tv))
extractPattAnnot δ π0
  | pattHasAnnot π0 = Just <$> loop π0
  | otherwise       = return Nothing
  where
  loop (VarPa _)    = newTVTy
  loop WldPa        = newTVTy
  loop (ConPa n πs) = ConTy n <$> mapM loop πs
  loop (InjPa n π)  = RowTy n <$> loop π <*> newTVTy
  loop (AnnPa _ an) = instAnnot δ an

-- | Given a list of type/U-action pairs, run all the U actions, but
--   in an order that does all U-actions not assocated with tyvars
--   before those associated with tyvars. Checks dynamically after each
--   action, since an action can turn a tyvar into a non-tyvar.
subsumeN ∷ MonadC tv r m ⇒ [(Type tv, m ())] → m ()
subsumeN [] = return ()
subsumeN σs = subsumeOneOf σs >>= subsumeN
  where
    subsumeOneOf []             = return []
    subsumeOneOf [(_, u1)]      = [] <$ u1
    subsumeOneOf ((σ1, u1):σs)  = do
      σ ← substRoot σ1
      case σ of
        VarTy (FreeVar α) | tvFlavorIs Universal α
          → ((σ, u1):) <$> subsumeOneOf σs
        _ → σs <$ u1

-- | Given a function arity and a type, extracts a list of argument
--   types and a result type of at most the given arity.
funmatchN ∷ MonadC tv r m ⇒ Int → Type tv → m ([Type tv], Type tv)
funmatchN n0 σ = do
  σ' ← substRoot σ
  case σ' of
    ConTy "->" [_, _, _] → unroll n0 σ'
    VarTy (FreeVar α) | tvFlavorIs Universal α → do
      β1 ← newTVTy
      qe ← newTV' QualKd
      β2 ← newTVTy
      σ' =: arrTy β1 (qvarexp (FreeVar qe)) β2
      return ([β1], β2)
    RecTy _ σ1 →
      funmatchN n0 (openTy 0 [σ'] σ1)
    _ → fail $ "Type error: In application expression, expected " ++
               "operator to have a function type, but got ‘" ++
               show σ' ++ "’ instead"
  where
    unroll n (ConTy "->" [σ1, _, σ']) | n > 0 = do
      (σ2m, σ) ← unroll (n - 1) =<< substRoot σ'
      return (σ1:σ2m, σ)
    unroll _ σ                           = return ([], σ)

-- | Subsumption
(≤)   ∷ MonadC tv r m ⇒ Type tv → Type tv → m ()
σ1 ≤ σ2 = do
  traceN 2 ("≤", σ1, σ2)
  subsumeBy (<:) σ1 σ2

subsumeBy ∷ MonadC tv r m ⇒
            (Type tv → Type tv → m ()) → Type tv → Type tv → m ()
subsumeBy (<*) σ1 σ2 = do
  σ1' ← substRoot σ1
  σ2' ← substRoot σ2
  case (σ1', σ2') of
    (VarTy (FreeVar α), _) | tvFlavorIs Universal α → do
      σ1' <* σ2'
    (_, VarTy (FreeVar α)) | tvFlavorIs Universal α → do
      σ1' ← instAll True =<< substDeep σ1'
      σ1' <* σ2'
    _ → do
      ρ1        ← instantiate σ1'
      (ρ2, αs2) ← collectTV (instantiateNeg σ2')
      ρ1 <* ρ2
      let (us1, _, ss1) = partitionFlavors αs2
      freeSkolems ← Set.filter (tvFlavorIs Skolem) <$>
                      ftvSet (σ1, σ2, fvTy <$> us1)
      when (any (`Set.member` freeSkolems) ss1) $ do
        traceN 3 (αs2, freeSkolems)
        fail $ "Type error: cannot subsume type ‘" ++ show σ1 ++
               "’ to type ‘" ++ show σ2 ++ "’ because the former is " ++
               "insufficiently polymorphic."
      return ()

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
--- Conditional generalization/instantiation
---

-- We start with a system for specifying requested
-- generalization/instantiation

-- | Used by 'infer' and helpers to specify a requested
--   generalization/instantiation state.
data Request tv
  = Request {
      -- | Request the type to have ∀ quantifiers generalized
      rqAll  ∷ !Bool,
      -- | Request the type to have ∃ quantifiers generalized
      rqEx   ∷ !Bool,
      -- | Require that the existentials type variables among these
      --   type variables be generalizable
      rqTVs  ∷ [(tv, Rank.Rank)],
      -- | Rank to which to generalize
      rqRank ∷ !Rank.Rank
    }

instance Ppr tv ⇒ Ppr (Request tv) where
  ppr φ = (if rqAll φ then Ppr.char '∀' else Ppr.empty)
          Ppr.<>
          (if rqEx φ then Ppr.char '∃' else Ppr.empty)
          Ppr.<>
          (if null (rqTVs φ)
             then Ppr.empty
             else ppr (rqTVs φ) Ppr.<> Ppr.char '/' Ppr.<> ppr (rqRank φ))

-- | Defines a variadic function for building 'Request' states.  Minimal
--   definition: 'addToRequest'
class MkRequest r tv | r → tv where
  -- | Variadic function that constructs a 'Request' state given some
  --   number of parameters to modify it, as shown by instances below.
  request      ∷ r
  request      = addToRequest Request {
    rqAll       = False,
    rqEx        = False,
    rqTVs       = [],
    rqRank      = Rank.infinity
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

{-
instance MkRequest r tv ⇒ MkRequest (Γ tv' → r) tv where
  addToRequest r γ = addToRequest r (rankΓ γ)
  -}

instance MkRequest r tv ⇒ MkRequest (Quant → r) tv where
  addToRequest r AllQu = addToRequest r { rqAll = True }
  addToRequest r ExQu  = addToRequest r { rqEx = True }

-- 'maybeGen', 'maybeInst', and 'maybeInstGen' are the external
-- interface to conditional generalization.

-- | Generalize the requested flavors, 
maybeGen ∷ MonadC tv r m ⇒
           Term Empty → Request tv → Γ tv → Type tv → m (Type tv)
maybeGen e0 φ γ σ = do
  let value = syntacticValue e0
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

maybeInstGen ∷ MonadC tv r m ⇒
               Term Empty → Request tv → Γ tv → Type tv → m (Type tv)
maybeInstGen e φ γ σ = do
  σ ← case () of
    _ | isAnnotated e → return σ
      | rqAll φ       → return σ
      | rqEx φ        → instAll True =<< substDeep σ
      | otherwise     → instantiate σ
  maybeGen e φ γ σ

-- | Check for escaping existential type variables
checkEscapingEx ∷ MonadC tv r m ⇒ Request tv → m ()
checkEscapingEx φ =
  for_ (rqTVs φ) $ \(α,rank) → do
    rank' ← getTVRank α
    when (rank' <= rank) $
      fail "Type error: Existential type variable escapes its scope."

---
--- Instantiation operations
---

-- | Given a type relation, (maybe) a type, a type constructor name,
--   and its arity, return a list of (maybe) parameter types and returns
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
splitCon ∷ MonadC tv r m ⇒
           (Type tv → Type tv → m ()) →
           Maybe (Type tv) → Name → Int →
           m ([Maybe (Type tv)])
splitCon _    Nothing  _ arity = return (replicate arity Nothing)
splitCon (<*) (Just σ) c arity = do
  traceN 4 ("splitCon", σ, c, arity)
  ρ ← instAllEx True False =<< substDeep σ
  case ρ of
    ConTy c' σs       | c == c', length σs == arity
      → return (Just <$> σs)
    ConTy _ []
      → do
          ρ <* ConTy c []
          return []
    VarTy (FreeVar α) | tvFlavorIs Universal α
      → do
          αs ← replicateM arity (newTVTy' (tvDescr α))
          ρ <* ConTy c αs
          return (Just <$> αs)
    _ → fail $ "Type error: Pattern expected a value constructed " ++
               "with ‘" ++ c ++ "’ (arity " ++ show arity ++ ") " ++
               "but got type ‘" ++ show σ ++ "’ instead."

-- | Like 'splitCon', but for rows.
--   PRECONDITION: σ is fully substituted.
splitRow ∷ MonadC tv r m ⇒
           (Type tv → Type tv → m ()) →
           Maybe (Type tv) → Name →
           m (Maybe (Type tv), Maybe (Type tv))
splitRow _    Nothing  _    = return (Nothing, Nothing)
splitRow (<*) (Just σ) name = do
  traceN 4 ("splitRow", σ, name)
  ρ ← instAllEx True False =<< substDeep σ
  loop ρ
  where
  loop ρ = case ρ of
    RowTy name' τ1 τ2 | name' == name
      → return (Just τ1, Just τ2)
                      | otherwise
      → do
        (mτ1, mτ2) ← loop τ2
        return (mτ1, RowTy name' τ1 <$> mτ2)
    VarTy (FreeVar α) | tvFlavorIs Universal α
      → do
          τ1 ← newTVTy
          τ2 ← newTVTy
          ρ <* RowTy name τ1 τ2
          return (Just τ1, Just τ2)
    _ → fail $ "Type error: Pattern expected a value constructed " ++
               "with ‘`" ++ name ++ "’ but got type ‘" ++ show σ ++
               "’ instead."

-- | Given a map from type variables names and qualifiers to variances,
--   create an initial type variable environment.
instAnnotTVs ∷ MonadC tv r m ⇒ VarMap (Name, QLit) → m (Δ tv)
instAnnotTVs vmap = foldM each Map.empty (Map.toList vmap) where
  each δ ((name, ql), variance) = do
    α ← newTV' (ql, varianceToKind variance,
                "annotation type variable " ++ qLitSigil ql : name)
    case Map.insertLookupWithKey (\_ _ → id) name α δ of
      (Nothing, δ') → return δ'
      (Just _,  _)  → fail $
        "Type error: Used both type variables `" ++ name ++
        " and '" ++ name ++ " in annotations in same expression."

-- | Given a tyvar environment (mapping some-bound names to tyvars) and
--   an annotation, create new universal type variables for any new
--   some-bound names in the annotation and update the environment
--   accordingly. Return the annotation instantiated to a type and the
--   list of universal tyvars.
instAnnot ∷ MonadTV tv r m ⇒
            Δ tv → Annot → m (Type tv)
instAnnot δ (Annot nqls σ0) = do
  let names = fst <$> nqls
  αs ← mapM eachName names
  traverse_ reportTV αs
  let σ = totalSubst names (fvTy <$> αs) =<< σ0
  traceN 4 ("instAnnot", δ, σ, αs)
  return σ
  where
    eachName ('_':_) = newTV
    eachName name    = case Map.lookup name δ of
      Just α  → return α
      Nothing → fail "BUG! (instAnnot): type variable not found"

-- | Instantiate the outermost universal and existential quantifiers
--   at the given polarities.
--   PRECONDITION: σ is fully substituted.
instAllEx ∷ MonadC tv r m ⇒ Bool → Bool → Type tv → m (Type tv)
instAllEx upos epos = substDeep >=> instEx epos >=> instAll upos

-- | Instantiate an outer universal quantifier.
--   PRECONDITION: σ is fully substituted.
instAll ∷ MonadC tv r m ⇒ Bool → Type tv → m (Type tv)
instAll pos (QuaTy AllQu αqs σ) = do
  traceN 4 ("instAll/∀", pos, αqs, σ)
  instGeneric 0 (determineFlavor AllQu pos) αqs σ
instAll pos (QuaTy ExQu αqs (QuaTy AllQu βqs σ)) = do
  traceN 4 ("instAll/∃∀", pos, αqs, βqs, σ)
  QuaTy ExQu αqs <$> instGeneric 1 (determineFlavor AllQu pos) βqs σ
instAll _ σ = return σ

-- | Instantiate an outer existential quantifier.
--   PRECONDITION: σ is fully substituted.
instEx ∷ MonadC tv r m ⇒ Bool → Type tv → m (Type tv)
instEx pos (QuaTy ExQu αqs σ) = do
  traceN 4 ("instEx", pos, αqs, σ)
  instGeneric 0 (determineFlavor ExQu pos) αqs σ
instEx _ σ = return σ

-- | What kind of type variable to create when instantiating
--   a given quantifier in a given polarity:
determineFlavor ∷ Quant → Bool → Flavor
determineFlavor AllQu  True    = Universal
determineFlavor AllQu  False   = Skolem
determineFlavor ExQu   True    = Existential
determineFlavor ExQu   False   = Universal

-- | Instantiate type variables and use them to open a type, given
--   a flavor and list of qualifier literal bounds.  Along with the
--   instantiated type, returns any new type variables.
--   PRECONDITION: σ is fully substituted.
instGeneric ∷ MonadC tv r m ⇒
              Int → Flavor → [(a, QLit)] → Type tv →
              m (Type tv)
instGeneric k flav αqs σ = do
  αs ← zipWithM (newTV' <$$> (,flav,) . snd) αqs (inferKindsTy σ)
  return (openTy k (fvTy <$> αs) σ)

-- | To instantiate a prenex quantifier with fresh type variables.
instantiate ∷ MonadC tv r m ⇒ Type tv → m (Type tv)
instantiate = instAllEx True True

-- | To instantiate a prenex quantifier with fresh type variables, in
--   a negative position
instantiateNeg ∷ MonadC tv r m ⇒ Type tv → m (Type tv)
instantiateNeg = instAllEx False False

---
--- Testing functions
---

check ∷ String → IO ()
check e = case showInfer (read e) of
  Left err    → fail err
  Right (τ,c) →
    putStrLn $ show τ ++ if null c then "" else " constraint " ++ c

showInfer ∷ Term Empty → Either String (Type String, String)
showInfer e = runU $ do
  (τ, c) ← inferTm (emptyΓ &+& Map.fromList γ0) e
  τ'     ← stringifyType τ
  return (τ', c)

stringifyType ∷ MonadTV tv r m ⇒ Type tv → m (Type String)
stringifyType = foldType (mkQuaF QuaTy) (mkBvF bvTy) (fvTy . show)
                         ConTy RowTy (mkRecF RecTy)
-}
