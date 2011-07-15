{-#
  LANGUAGE
    FlexibleInstances,
    FunctionalDependencies,
    GeneralizedNewtypeDeriving,
    MultiParamTypeClasses,
    ParallelListComp,
    QuasiQuotes,
    RankNTypes,
    UndecidableInstances,
    UnicodeSyntax,
    ViewPatterns
  #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Statics.Constraint (
  -- * The constraint solver interface
  MonadConstraint(..), generalize, generalizeList, generalizeEx,

  -- * An implementation of the interface
  ConstraintT,
  runConstraintT, mapConstraintT,
  ConstraintState, constraintState0,
) where

import Util
import Util.Trace
import Util.MonadRef
import AST ( isQVariance )
import qualified Syntax.Ppr      as Ppr
import qualified Alt.Graph       as Gr
import qualified Data.UnionFind  as UF
import Type
import Statics.Error

import Prelude ()
import qualified Data.List  as List
import qualified Data.Set   as S
import qualified Data.Map   as M
import qualified Data.Boolean.SatSolver as SAT

---
--- A CONSTRAINT-SOLVING MONAD
---

class MonadSubst tv r m ⇒ MonadConstraint tv r m | m → tv r where
  -- | Subtype and equality constraints
  (<:), (=:)    ∷ Type tv → Type tv → m ()
  -- | Subqualifier constraint
  (⊏:), (~:)    ∷ (Qualifier q1 tv, Qualifier q2 tv) ⇒ q1 → q2 → m ()
  -- | Constrain by the given variance
  relate        ∷ Variance → Type tv → Type tv → m ()
  --
  τ1 =: τ2   = τ1 <: τ2 >> τ2 <: τ1
  τ1 ~: τ2   = τ1 ⊏: τ2 >> τ2 ⊏: τ1
  relate variance τ1 τ2 = case variance of
    Covariant      → τ1 <: τ2
    Contravariant  → τ2 <: τ1
    Invariant      → τ1 =: τ2
    QCovariant     → τ1 ⊏: τ2
    QContravariant → τ2 ⊏: τ1
    QInvariant     → τ1 ~: τ2
    Omnivariant    → return ()
  --
  -- | Get the set of pinned type variables.
  getPinnedTVs    ∷ m (S.Set tv)
  -- | Run a computation in the context of some "pinned down" type
  --   variables, which means that they won't be considered for
  --   elimination or generalization.
  withPinnedTVs   ∷ Ftv a tv ⇒ a → m b → m b
  -- | Update the list of pinned type variables to reflect a substitution.
  --   PRECONDITION: τ is substituted.
  updatePinnedTVs ∷ tv → Type tv → m ()
  --
  -- | Figure out which variables to generalize in a piece of syntax.
  --   The 'Bool' indicates whether the syntax whose type is being
  --   generalized is a syntactic value.  Returns a list of
  --   generalizable variables and their qualifier bounds.
  generalize'     ∷ Bool → Rank → Type tv → m [(tv, QLit)]
  --
  -- | Return a string representation of the constraint
  showConstraint  ∷ m Ppr.Doc

infix 5 <:, =:, ⊏:, ~:

--
-- Pass-through instances
--

instance (MonadConstraint tv s m, Monoid w) ⇒
         MonadConstraint tv s (WriterT w m) where
  (<:) = lift <$$> (<:)
  (=:) = lift <$$> (=:)
  (⊏:) = lift <$$> (⊏:)
  (~:) = lift <$$> (~:)
  getPinnedTVs   = lift getPinnedTVs
  withPinnedTVs  = mapWriterT <$> withPinnedTVs
  updatePinnedTVs= lift <$$> updatePinnedTVs
  generalize'    = lift <$$$> generalize'
  showConstraint = lift showConstraint

instance MonadConstraint tv r m ⇒
         MonadConstraint tv r (StateT s m) where
  (<:) = lift <$$> (<:)
  (=:) = lift <$$> (=:)
  (⊏:) = lift <$$> (⊏:)
  (~:) = lift <$$> (~:)
  getPinnedTVs   = lift getPinnedTVs
  withPinnedTVs  = mapStateT <$> withPinnedTVs
  updatePinnedTVs= lift <$$> updatePinnedTVs
  generalize'    = lift <$$$> generalize'
  showConstraint = lift showConstraint

instance MonadConstraint tv p m ⇒
         MonadConstraint tv p (ReaderT r m) where
  (<:) = lift <$$> (<:)
  (=:) = lift <$$> (=:)
  (⊏:) = lift <$$> (⊏:)
  (~:) = lift <$$> (~:)
  getPinnedTVs   = lift getPinnedTVs
  withPinnedTVs  = mapReaderT <$> withPinnedTVs
  updatePinnedTVs= lift <$$> updatePinnedTVs
  generalize'    = lift <$$$> generalize'
  showConstraint = lift showConstraint

instance (MonadConstraint tv p m, Monoid w) ⇒
         MonadConstraint tv p (RWST r w s m) where
  (<:) = lift <$$> (<:)
  (=:) = lift <$$> (=:)
  (⊏:) = lift <$$> (⊏:)
  (~:) = lift <$$> (~:)
  getPinnedTVs   = lift getPinnedTVs
  withPinnedTVs  = mapRWST <$> withPinnedTVs
  updatePinnedTVs= lift <$$> updatePinnedTVs
  generalize'    = lift <$$$> generalize'
  showConstraint = lift showConstraint

--
-- Some generic operations
--

-- | Generalize a type under a constraint and environment,
--   given whether the the value restriction is satisfied or not
generalize    ∷ MonadConstraint tv r m ⇒
                Bool → Rank → Type tv → m (Type tv)
generalize value γrank ρ = do
  αqs ← generalize' value γrank ρ
  standardizeMus <$> closeQuant Forall αqs <$> subst ρ

-- | Generalize a list of types together.
generalizeList ∷ MonadConstraint tv r m ⇒
                 Bool → Rank → [Type tv] → m [Type tv]
generalizeList value γrank ρs = do
  αqs ← generalize' value γrank (foldl tyTuple tyUnit ρs)
  mapM (standardizeMus <$> closeQuant Forall αqs <$$> subst) ρs

-- | Generalize the existential type variables in a type
generalizeEx   ∷ MonadConstraint tv r m ⇒
                 Rank → Type tv → m (Type tv)
generalizeEx γrank ρ0 = do
  ρ   ← subst ρ0
  αs  ← removeByRank γrank (filter (tvFlavorIs Existential) (ftvList ρ))
  αqs ← mapM addQual αs
  return (closeQuant Exists αqs ρ)
  where
    addQual α = case tvQual α of
      Just ql → return (α, ql)
      Nothing → typeBug "generalizeEx"
                        "existential type variable with no rank"

-- | Remove type variables from a list if their rank indicates that
--   they're in the environment or if they're pinned
removeByRank ∷ MonadConstraint tv r m ⇒ Rank → [tv] → m [tv]
removeByRank γrank αs = do
  pinned ← getPinnedTVs
  let keep α = do
        rank ← getTVRank α
        return (rank > γrank && α `S.notMember` pinned)
  filterM keep αs

---
--- SUBTYPING CONSTRAINT SOLVER
---

--
-- The internal state
--

-- | The state of the constraint solver.
data CTState tv r
  = CTState {
      -- | Graph for subtype constraints on type variables and atomic
      --   type constructors
      csGraph   ∷ !(Gr.Gr tv ()),
      -- | Reverse lookup for turning atoms into node numbers for the
      --   'csGraph' graph
      csNodeMap ∷ !(Gr.NodeMap tv),
      -- | Maps type variables to same-size equivalence classes
      csEquivs  ∷ !(ProxyMap tv r),
      -- | Types to relate by the subqualifier relation
      csQuals   ∷ ![(Type tv, Type tv)],
      -- | Stack of pinned type variables
      csPinned  ∷ ![S.Set tv]
    }

-- | Representation of type variable equivalence class
type TVProxy  tv r = UF.Proxy r (S.Set tv)
-- | The map from type variables to equivalence classes
type ProxyMap tv r = M.Map tv (TVProxy tv r)

-- | Updater for 'csQuals' field
csQualsUpdate ∷ ([(Type tv, Type tv)] → [(Type tv, Type tv)]) →
                CTState tv r → CTState tv r
csQualsUpdate f cs = cs { csQuals = f (csQuals cs) }

-- | Updater for 'csEquivs' field
csEquivsUpdate ∷ (ProxyMap tv r → ProxyMap tv r) →
                 CTState tv r → CTState tv r
csEquivsUpdate f cs = cs { csEquivs = f (csEquivs cs) }

-- | Updater for 'csPinned' field
csPinnedUpdate ∷ ([S.Set tv] → [S.Set tv]) →
                 CTState tv r → CTState tv r
csPinnedUpdate f cs = cs { csPinned = f (csPinned cs) }

instance Tv tv ⇒ Show (CTState tv r) where
  showsPrec _ cs
    | null (Gr.edges (csGraph cs)) && null (csQuals cs)
        = id
    | otherwise
        = showString "CTState { csGraph = "
        . shows (Gr.ShowGraph (csGraph cs))
        . showString ", csQuals = "
        . shows (csQuals cs)
        . showString " }"

instance Tv tv ⇒ Ppr.Ppr (CTState tv r) where
  ppr cs = Ppr.ppr . M.fromList $
    [ ("graph",    Ppr.fsep . Ppr.punctuate Ppr.comma $
                     [ Ppr.pprPrec 10 α1
                         Ppr.<> Ppr.text "<:"
                         Ppr.<> Ppr.pprPrec 10 α2
                     | (α1, α2) ← Gr.labNodeEdges (csGraph cs) ])
    , ("quals",    Ppr.fsep . Ppr.punctuate Ppr.comma $
                     [ Ppr.pprPrec 9 τ1
                         Ppr.<> Ppr.char '⊑'
                         Ppr.<> Ppr.pprPrec 9 τ2
                     | (τ1, τ2) ← csQuals cs ])
    ]

--
-- The monad transformer
--

-- | Underlying 'ConstraintT' is a monad transformer that carries merely
--   the constraint-solving state.
newtype ConstraintT_ tv r m a
  = ConstraintT_ {
      unConstraintT_ ∷ StateT (CTState tv r) m a
    }
  deriving (Functor, Applicative, Monad, MonadAlmsError, MonadTrace)

-- | Map some higher-order operation through 'ConstraintT_'.
mapConstraintT_   ∷ (∀ s. m (a, s) → n (b, s)) →
                    ConstraintT_ tv r m a → ConstraintT_ tv r n b
mapConstraintT_ f = ConstraintT_ . mapStateT f .  unConstraintT_

-- | Constraint monad transformer carries constraint solver state.
--   'SubstT' substitution state.
type ConstraintT tv r m = ConstraintT_ tv r (SubstT r m)

-- | Map some higher-order operation through 'ConstraintT'.
mapConstraintT   ∷ (Functor m, Functor n) ⇒
                   (∀ s. m (a, s) → n (b, s)) →
                   ConstraintT tv r m a → ConstraintT tv r n b
mapConstraintT f = mapConstraintT_ (mapSubstT f')
  where
    f' action            = unshift <$> f (shift <$> action)
    shift ((a, s), s')   = (a, (s, s'))
    unshift (a, (s, s')) = ((a, s), s')

-- | Run the constraint solver.
runConstraintT ∷ (MonadAlmsError m, MonadRef r m) ⇒
                 ConstraintState (TV r) r →
                 ConstraintT (TV r) r m a →
                 m (a, ConstraintState (TV r) r)
runConstraintT ecs m = do
  ((result, cs), ss) ← runSubstT
                          (ecsSubst ecs)
                          (runStateT (unConstraintT_ (resetEquivTVs >> m))
                                     (ecsInternal ecs))
  return (result, ExternalConstraintState cs ss)

-- | The external representation of the constraint solver's state
data ConstraintState tv r
  = ExternalConstraintState {
      ecsInternal       ∷ !(CTState tv r),
      ecsSubst          ∷ !SubstState
    }

-- | The initial constraint solver state
constraintState0 ∷ Tv tv ⇒ ConstraintState tv r
constraintState0
  = ExternalConstraintState {
      ecsInternal = CTState {
        csGraph   = Gr.empty,
        csNodeMap = Gr.new,
        csEquivs  = M.empty,
        csQuals   = [],
        csPinned  = []
      },
      ecsSubst = substState0
    }

instance Tv tv ⇒ Ppr.Ppr (ConstraintState tv r) where
  ppr = Ppr.ppr . ecsInternal

instance Tv tv ⇒ Show (ConstraintState tv r) where
  showsPrec = Ppr.showFromPpr

--
-- Instances
--

-- | Transformer instance
instance MonadTrans (ConstraintT_ tv r) where
  lift = ConstraintT_ . lift

-- | Pass through for reference operations
instance MonadSubst tv r m ⇒
         MonadRef r (ConstraintT_ tv r m) where
  newRef        = lift <$> newRef
  readRef       = lift <$> readRef
  writeRef      = lift <$$> writeRef

-- | Pass through for unification operations
instance MonadSubst tv r m ⇒
         MonadSubst tv r (ConstraintT_ tv r m) where
  newTV_ (Universal, kind, bound, descr) = do
    α ← lift (newTV' (kind, descr))
    fvTy α ⊏: bound
    return α
  newTV_ attrs  = lift (newTV' attrs)
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  collectTVs    = mapConstraintT_ (mapListen2 collectTVs)
  reportTVs     = lift . reportTVs
  monitorChange = mapConstraintT_ (mapListen2 monitorChange)
  setChanged    = lift setChanged

-- | 'ConstraintT' implements 'Graph'/'NodeMap' transformer operations
--   for accessing its graph and node map.
instance (Ord tv, Monad m) ⇒
         Gr.MonadNM tv () Gr.Gr (ConstraintT_ tv r m) where
  getNMState = ConstraintT_ (gets (csNodeMap &&& csGraph))
  getNodeMap = ConstraintT_ (gets csNodeMap)
  getGraph   = ConstraintT_ (gets csGraph)
  putNMState (nm, g) = ConstraintT_ . modify $ \cs →
    cs { csNodeMap = nm, csGraph = g }
  putNodeMap nm = ConstraintT_ . modify $ \cs → cs { csNodeMap = nm }
  putGraph g    = ConstraintT_ . modify $ \cs → cs { csGraph = g }

-- | Constraint solver implementation.
instance MonadSubst tv r m ⇒
         MonadConstraint tv r (ConstraintT_ tv r m) where
  τ <: τ' = do
    traceN 3 ("<:", τ, τ')
    runSeenT (subtypeTypes False τ τ')
  τ =: τ' = do
    traceN 3 ("=:", τ, τ')
    runSeenT (subtypeTypes True τ τ')
  τ ⊏: τ' = do
    traceN 3 ("⊏:", qualToType τ, qualToType τ')
    ConstraintT_ . modify . csQualsUpdate $
      ((qualToType τ, qualToType τ') :)
  --
  getPinnedTVs      = S.unions <$> ConstraintT_ (gets csPinned)
  --
  withPinnedTVs a m = do
    let αs = ftvSet a
    ConstraintT_ (modify (csPinnedUpdate (αs :)))
    result ← m
    ConstraintT_ (modify (csPinnedUpdate tail))
    return result
  --
  updatePinnedTVs α τ = do
    let βs      = ftvSet τ
        update  = snd . mapAccumR eachSet False
        eachSet False set
          | α `S.member` set = (True, βs `S.union` S.delete α set)
        eachSet done set       = (done, set)
    ConstraintT_ (modify (csPinnedUpdate update))
  --
  generalize'    = solveConstraint
  --
  showConstraint = Ppr.ppr <$> ConstraintT_ get

{-# INLINE gtraceN #-}
gtraceN ∷ (TraceMessage a, Tv tv, MonadTrace m) ⇒
          Int → a → ConstraintT_ tv r m ()
gtraceN =
  if debug then \n info →
    if n <= debugLevel then do
      trace info
      cs ← ConstraintT_ get
      let doc = Ppr.ppr cs
      unless (Ppr.isEmpty doc) $
        trace (Ppr.nest 4 doc)
    else return ()
  else \_ _ → return ()

-- | Monad transformer for tracking which type comparisons we've seen,
--   in order to implement recursive subtyping.  A pair of types mapped
--   to @True@ means that they're known to be equal, whereas @False@
--   means that they're only known to be subtyped.
type SeenT tv r m = StateT (M.Map (Type tv, Type tv) Bool)
                           (ConstraintT_ tv r m)

-- | Run a recursive subtyping computation.
runSeenT ∷ (Tv tv, MonadTrace m) ⇒ SeenT tv r m a → ConstraintT_ tv r m a
runSeenT m = do
  gtraceN 4 "runSeenT {"
  result ← evalStateT m M.empty
  gtraceN 4 "} runSeenT"
  return result

-- | Relate two types at either subtyping or equality, depending on
--   the value of the first parameter (@True@ means equality).
--   This eagerly solves as much as possible, adding to the constraint
--   only as necessary.
subtypeTypes ∷ MonadSubst tv r m ⇒
               Bool → Type tv → Type tv → SeenT tv r m ()
subtypeTypes unify = check where
  check τ1 τ2 = do
    lift $ gtraceN 4 ("subtypeTypes", unify, τ1, τ2)
    τ1'  ← subst τ1
    τ2'  ← subst τ2
    seen ← get
    unless (M.lookup (τ1', τ2') seen >= Just unify) $ do
      put (M.insert (τ1', τ2') unify seen)
      decomp τ1' τ2'
  --
  decomp τ1 τ2 = case (τ1, τ2) of
    (TyVar v1, TyVar v2)
      | v1 == v2 → return ()
    (TyVar (Free r1), TyVar (Free r2))
      | tvFlavorIs Universal r1, tvFlavorIs Universal r2 →
      if unify
        then unifyVar r1 (fvTy r2)
        else do
          lift (makeEquivTVs r1 r2)
          addEdge r1 r2
    (TyVar (Free r1), _)
      | tvFlavorIs Universal r1 → do
      τ2' ← lift $ occursCheck r1 τ2 >>= if unify then return else copyType
      unifyVar r1 τ2'
      unless unify (check τ2' τ2)
    (_, TyVar (Free r2))
      | tvFlavorIs Universal r2 → do
      τ1' ← lift $ occursCheck r2 τ1 >>= if unify then return else copyType
      unifyVar r2 τ1'
      unless unify (check τ1 τ1')
    (TyQu Forall αs1 τ1', TyQu Forall αs2 τ2')
      | if unify
          then αs1 == αs2
          else length αs1 == length αs2
            && and (zipWith ((⊒)`on`snd) αs1 αs2) →
      check τ1' τ2'
    (TyQu Exists αs1 τ1', TyQu Exists αs2 τ2')
      | αs1 == αs2 →
      check τ1' τ2'
    (TyApp tc1 τs1, TyApp tc2 τs2)
      | tc1 == tc2 && length τs1 == length τs2 →
      sequence_
        [ if unify
            then if isQVariance var
              then τ1' ~: τ2'
              else check τ1' τ2'
            else relateTypes var τ1' τ2'
        | var ← tcArity tc1
        | τ1' ← τs1
        | τ2' ← τs2 ]
      | Just (τ1', τ2') ← matchTyCons τ1 τ2 →
      check τ1' τ2'
    (TyRow n1 τ11 τ12, TyRow n2 τ21 τ22)
      | n1 == n2 → do
        check τ11 τ21
        check τ12 τ22
      | otherwise   → do
        α ← newTVTy
        check (TyRow n1 τ11 α) τ22
        β ← newTVTy
        check τ12 (TyRow n2 τ21 β)
        check α β
    (TyMu _ τ1', _) →
      decomp (openTy 0 [τ1] τ1') τ2
    (_, TyMu _ τ2') →
      decomp τ1 (openTy 0 [τ2] τ2')
    _ →
      tErrExp
        (if unify
           then [msg| Cannot unify: |]
           else [msg| Cannot subtype: |])
        (pprMsg τ1)
        (pprMsg τ2)
  --
  addEdge a1 a2 = do
    Gr.insNewMapNodeM a1
    Gr.insNewMapNodeM a2
    Gr.insMapEdgeM (a1, a2, ())

-- | Relate two types at the given variance.
relateTypes ∷ MonadSubst tv r m ⇒
              Variance → Type tv → Type tv → SeenT tv r m ()
relateTypes var = case var of
  Invariant     → subtypeTypes True
  Covariant     → subtypeTypes False
  Contravariant → flip (subtypeTypes False)
  QInvariant    → (~:)
  QCovariant    → (⊏:)
  QContravariant→ flip (⊏:)
  Omnivariant   → \_ _ → return ()

-- | Copy a type while replacing all the type variables with fresh ones
--   of the same kind.
copyType ∷ MonadSubst tv r m ⇒ Type tv → m (Type tv)
copyType =
   foldTypeM (mkQuF (return <$$$> TyQu))
             (mkBvF (return <$$$> bvTy))
             fvar
             fcon
             (return <$$$> TyRow)
             (mkMuF (return <$$> TyMu))
  where
    fvar α | tvFlavorIs Universal α = newTVTy' (tvKind α)
           | otherwise              = return (fvTy α)
    -- Nullary type constructors that are involved in the atomic subtype
    -- relation are converted to type variables:
    fcon tc τs
      = TyApp tc <$> sequence
          [ -- A Q-variant type constructor parameter becomes a single
            -- type variable:
            if isQVariance var
              then newTVTy' KdQual
              else return τ
          | τ   ← τs
          | var ← tcArity tc ]

-- | Unify a type variable with a type, where the type must be locally
--   closed.
--   ASSUMPTIONS: @α@ has not been substituted and the occurs check has
--   already passed.
unifyVar ∷ MonadSubst tv r m ⇒ tv → Type tv → SeenT tv r m ()
unifyVar α τ0 = do
  lift $ gtraceN 4 ("unifyVar", α, τ0)
  τ ← subst τ0
  tassert (lcTy 0 τ)
    [msg|
      Cannot unify because a $τ is insufficiently polymorphic
    |]
  writeTV α τ
  lift (updatePinnedTVs α τ)
  (n, _) ← Gr.mkNodeM α
  gr     ← Gr.getGraph
  case Gr.match n gr of
    (Nothing,                 _)   → return ()
    (Just (pres, _, _, sucs), gr') → do
      Gr.putGraph gr'
      sequence_ $
        [ case Gr.lab gr' n' of
            Nothing → return ()
            Just a  → subtypeTypes False (fvTy a) τ
        | (_, n') ← pres ]
        ++
        [ case Gr.lab gr' n' of
            Nothing → return ()
            Just a  → subtypeTypes False τ (fvTy a)
        | (_, n') ← sucs ]

--- OCCURS CHECK

-- | Performs the occurs check and returns a type suitable for unifying
--   with the given type variable, if possible.  This does the subtyping
--   occurs check, which checks not in terms of type variables but in
--   terms of same-size equivalence classes of type variables.
--   Unification is possible if all occurrences of type variables
--   size-equivalent to @α@ appear guarded by a type constructor that
--   permits recursion, in which case we roll up @τ@ as a recursive type
--   and return that.
occursCheck ∷ MonadSubst tv r m ⇒ tv → Type tv → ConstraintT_ tv r m (Type tv)
occursCheck α τ = do
  gtraceN 3 ("occursCheck", α, τ)
  let (guarded, unguarded) = (M.keys***M.keys) . M.partition id $ ftvG τ
  whenM (anyA (checkEquivTVs α) unguarded) $
    typeError [msg|
      Occurs check failed.
      Cannot construct an infinite type when unifying:
      <dl>
        <dt>type variable <dd>$α
        <dt>type          <dd>$τ
      </dl>
    |]
  recVars ← filterM (checkEquivTVs α) guarded
  when (not (null recVars)) $ gtraceN 3 ("occursCheck", "recvars", recVars)
  return (foldr closeRec τ recVars)

-- | Records that two type variables have the same size.
makeEquivTVs  ∷ MonadSubst tv r m ⇒ tv → tv → ConstraintT_ tv r m ()
makeEquivTVs α β = do
  pα ← getTVProxy α
  pβ ← getTVProxy β
  UF.coalesce_ (return <$$> S.union) pα pβ

-- | Checks whether two type variables have the same size.
checkEquivTVs ∷ MonadSubst tv r m ⇒ tv → tv → ConstraintT_ tv r m Bool
checkEquivTVs α β = do
  pα ← getTVProxy α
  pβ ← getTVProxy β
  UF.sameRepr pα pβ

-- | Clears all size-equivalence classes and rebuilds them based on the
--   current atomic subtyping constraint graph.
resetEquivTVs ∷ MonadSubst tv r m ⇒ ConstraintT_ tv r m ()
resetEquivTVs = do
  ConstraintT_ (modify (csEquivsUpdate (const M.empty)))
  g     ← Gr.getGraph
  mapM_ (uncurry makeEquivTVs)
        [ (α, β) | (α, β) ← Gr.labNodeEdges g ]

-- | Helper to get the proxy the represents the size-equivalence class
--   of a type variable.
getTVProxy ∷ MonadSubst tv r m ⇒ tv → ConstraintT_ tv r m (TVProxy tv r)
getTVProxy α = do
  equivs ← ConstraintT_ (gets csEquivs)
  case M.lookup α equivs of
    Just pα → return pα
    Nothing → do
      pα ← UF.create (S.singleton α)
      ConstraintT_ (modify (csEquivsUpdate (M.insert α pα)))
      return pα

--- CONSTRAINT SOLVING

-- | Solve a constraint as much as possible, returning the type
--   variables to generalize and their qualifier bounds.
solveConstraint ∷ MonadSubst tv r m ⇒
                  Bool → Rank → Type tv → ConstraintT_ tv r m [(tv, QLit)]
solveConstraint value γrank τ0 = do
  τ ← subst τ0
  let τftv = ftvV τ
  gtraceN 2 (TraceIn ("gen", "begin", value, γrank, τftv, τ))
  τftv ← coalesceSCCs τftv
  gtraceN 3 ("gen", "scc", τftv, τ)
  Gr.modifyGraph Gr.trcnr
  gtraceN 4 ("gen", "trc", τftv, τ)
  eliminateExistentials True (γrank, τftv)
  gtraceN 3 ("gen", "existentials 1", τftv, τ)
  untransitive
  gtraceN 3 ("gen", "untrans", τftv, τ)
  eliminateExistentials False (γrank, τftv)
  gtraceN 3 ("gen", "existentials 2", τftv, τ)
  τftv ← polarizedReduce τftv
  gtraceN 3 ("gen", "polarized", τftv, τ)
  eliminateExistentials False (γrank, τftv)
  gtraceN 3 ("gen", "existentials 3", τftv, τ)
  -- Guessing starts here
  τftv ← coalesceComponents value (γrank, τftv)
  gtraceN 3 ("gen", "components", τftv, τ)
  -- Guessing ends here
  qc    ← ConstraintT_ $ gets csQuals >>= mapM subst
  cftv  ← S.fromList . map snd <$> Gr.getsGraph Gr.labNodes
  αs    ← S.fromDistinctAscList <$>
            filter (tvFlavorIs Universal) <$>
              (removeByRank γrank
                (S.toAscList $ (ftvSet qc `S.union` M.keysSet τftv) S.\\ cftv))
  (qc, αqs, τ) ← solveQualifiers value αs qc τ
  ConstraintT_ (modify (csQualsUpdate (const qc)))
  gtraceN 2 (TraceOut ("gen", "finished", αqs, τ))
  resetEquivTVs
  return αqs
  where
    --
    -- Eliminate existentially-quantified type variables from the
    -- constraint
    eliminateExistentials trans (γrank, τftv) = do
      extvs ← getExistentials (γrank, τftv)
      traceN 4 ("existentials:", extvs)
      mapM (eliminateNode trans) (S.toList extvs)
    -- Get the existential type variables
    getExistentials (γrank, τftv) = do
      lnodes ← Gr.getsGraph Gr.labNodes
      cftv   ← removeByRank γrank [ α | (_, α) ← lnodes ]
      return (S.fromList cftv S.\\ M.keysSet τftv)
    -- Remove a node unless it is necessary to associate some of its
    -- neighbors -- in particular, a node with multiple predecessors
    -- but no successor (or dually, multiple successors but no
    -- predecessor) should not be removed.
    eliminateNode trans α = do
      (nm, g) ← Gr.getNMState
      let node = Gr.nmLab nm α
      case (Gr.pre g node, Gr.suc g node) of
        (_:_:_, []) → return ()
        ([], _:_:_) → return ()
        (pre, suc)  → do
          β ← newTVTy' KdQual
          writeTV α β
          traceN 4 ("eliminateNode",
                    catMaybes (map (Gr.lab g) pre),
                    β,
                    catMaybes (map (Gr.lab g) suc))
          sequence $
            [ fvTy α1 ⊏: β
            | n1 ← pre
            , let Just α1 = Gr.lab g n1 ]
            ++
            [ β ⊏: fvTy α2
            | n2 ← suc
            , let Just α2 = Gr.lab g n2 ]
          Gr.putGraph $
            let g' = Gr.delNode node g in
            if trans
              then g'
              else foldr ($) g'
                     [ Gr.insEdge (n1, n2, ())
                     | n1 ← pre
                     , n2 ← suc ]
    --
    -- Remove redundant edges:
    --  • Edges implied by transitivity
    untransitive = Gr.modifyGraph Gr.untransitive
    --
    -- Remove type variables based on polarity-related rules:
    --  • Coalesce positive type variables with a single predecessor
    --    and negative type variables with a single successor
    --  • Coalesce positive type variables that share all their
    --    predecessors and negative type variables that share all
    --    their successors.
    polarizedReduce = iterChanging $ \τftv → do
      nm ← Gr.getNodeMap
      foldM tryRemove τftv (findPolar nm τftv)
        where
        tryRemove τftv (n, α, var) = do
          let ln = (n, α)
          mτ ← readTV α
          g  ← Gr.getGraph
          case (mτ, Gr.gelem n g) of
            (Left _, True) →
              case (var, Gr.pre g n, Gr.suc g n) of
                -- Should we consider QCo(ntra)variance here too?
                (Covariant,     [pre], _)
                  → snd <$> coalesce ln (Gr.labelNode g pre) τftv
                (Contravariant, _,     [suc])
                  → snd <$> coalesce ln (Gr.labelNode g suc) τftv
                (Covariant,     pres,  _)
                  → siblings g τftv (ln,  1) pres (Gr.pre,Gr.suc)
                (Contravariant, _,     sucs)
                  → siblings g τftv (ln, -1) sucs (Gr.suc,Gr.pre)
                _ → return τftv
            _ → return τftv
        findPolar nm τftv = [ (Gr.nmLab nm α, α, var)
                            | (α, var) ← M.toList τftv
                            , var == 1 || var == -1 ]
        siblings g τftv (lnode@(n,_), var) pres (gpre, gsuc) = do
          lnodes ← liftM ordNub . runListT $ do
            pre ← ListT (return pres)
            sib ← ListT (return (gsuc g pre))
            guard $ sib /= n
            Just β ← return (Gr.lab g sib)
            guard $ M.lookup β τftv == Just var
            guard $ gpre g sib == pres
            return (sib, β)
          case lnodes of
            _:_ → do
                τftv' ← snd <$> coalesceList τftv (lnode:lnodes)
                return τftv'
            _   → return τftv
    --
    -- Coalesce the strongly-connected components to single atoms
    coalesceSCCs τftv = do
      foldM (liftM snd <$$> coalesceList) τftv =<< Gr.getsGraph Gr.labScc 
    -- Given a list of atoms, coalesce them to one atom
    coalesceList τftv0 (ln:lns) =
      foldM (\(ln1, state) ln2 → coalesce ln1 ln2 state) (ln, τftv0) lns
    coalesceList _      [] = typeBug "coalesceList" "Got []"
    -- Assign n2 to n1, updating the graph, type variables, and ftvs,
    -- and return whichever node survives
    -- PRECONDITION: α1 /= α2
    coalesce (n1, α1) (n2, α2) τftv = do
      τftv' ← assignTV α1 α2 τftv
      assignNode n1 n2
      return ((n2, α2), τftv')
    -- Update the graph to remove node n1, assigning all of its
    -- neighbors to n2
    assignNode n1 n2 = Gr.modifyGraph $ \g →
      Gr.insEdges [ (n', n2, ())
                  | n' ← Gr.pre g n1, n' /= n1, n' /= n2 ] $
      Gr.insEdges [ (n2, n', ())
                  | n' ← Gr.suc g n1, n' /= n1, n' /= n2 ] $
      Gr.delNode n1 g
    -- Update the type variables to assign β to α, updating the
    -- ftvs appropriately
    assignTV α β τftv = do
      writeTV α (fvTy β)
      updatePinnedTVs α (fvTy β)
      assignFtvMap α β τftv
    -- Given two type variables, where α ← β, update a map of free
    -- type variables to variance lists accordingly
    assignFtvMap α β vmap =
      case M.lookup α vmap of
        Just vs → return $ M.insertWith (+) β vs vmap'
        Nothing → return vmap
      where vmap' = M.delete α vmap
    -- Coalesce and remove fully-generalizable components
    coalesceComponents value (γrank, τftv) = do
      extvs  ← getExistentials (γrank, τftv)
      τcands ← genCandidates value τftv γrank
      let candidates = extvs `S.union` τcands
          each τftv component@(_:_)
            | all (`S.member` candidates) (map snd component)
            = do
                ((node, _), τftv')
                  ← coalesceList τftv component
                Gr.getGraph >>= Gr.putGraph . Gr.delNode node
                return τftv'
          each τftv _
            = return τftv
      foldM each τftv =<< Gr.getsGraph Gr.labComponents
    -- Find the generalization candidates, which are free in τ but
    -- not in γ (restricted further if not a value)
    genCandidates value τftv γrank =
      S.fromDistinctAscList <$>
        removeByRank γrank (map fst (M.toAscList (restrict τftv)))
        where
        restrict = if value
                     then id
                     else M.filter (`elem` [1, -1, 2, -2])

---
--- QUALIFIER CONSTRAINT SOLVING
---

{-

Syntactic metavariables:

 γ:  any type variable
 α:  generalization candidates
 β:  type variables with Q-variance
 δ:  generalization candidates with Q-variance
 q:  qualifier literals
 _s: a collection of _

 qe  ::=  q  |  γs  |  q γs     (qualifier expressions)

First rewrite as follows:

(DECOMPOSE)
  γs₁ \ γs₂ = γ₁ ... γⱼ
  βs  = { γ ∈ γs₂ | γ is Q-variant }
  βsᵢ = if γᵢ is Q-variant then γs₂ else βs
  -----------------------------------------------------------------------
  q₁ γs₁ ⊑ q₂ γs₂  --->  q₁ \-\ q₂ ⊑ βs ⋀ γ₁ ⊑ q₁ βs₁ ⋀ ... ⋀ γⱼ ⊑ q₁ βsᵢ

(BOT-SAT)
  ---------------
  U ⊑ βs  --->  ⊤

(TOP-SAT)
  -----------------
  γ ⊑ A βs  --->  ⊤

(BOT-UNSAT)
  q ≠ U
  -----------------
  q ⊑ U  --->  fail

(COMBINE-QLIT)
  --------------------------------------------
  γ ⊑ q ⋀ γ ⊑ q' ⋀ C; τ  --->  γ ⊑ q⊓q' ⋀ C; τ

(COMBINE-LE)
  q ⊑ q'   βs ⊆ βs'
  ---------------------------------------------------
  γ ⊑ q βs ⋀ γ ⊑ q' βs' ⋀ C; τ  --->  γ ⊑ q βs ⋀ C; τ

Then we have a constraint where each inequality is in one of two forms:

  γ ⊑ q βs
  q ⊑ βs

Now we continue to rewrite and perform substitutions as well.  Continue
to apply the above rules when they apply.  These new rewrites apply to a
whole constraint and type together, not to single atomic constraints.

For a type variable γ and type τ, let V(γ,τ) be γ's variance in τ.  We
also refer to the free type variables in only the lower or upper bounds
of a constraint C as lftv(C) and uftv(C), respectively.

These are non-lossy rewrites. Repeat them as much as possible,
continuing to apply the rewrites above when applicable:

(FORCE-U)
  -------------------------------
  β ⊑ U ⋀ C; τ  --->  [U/β](C; τ)

(SUBST-NEG)
  δ ∉ lftv(C)   V(δ,τ) ⊑ Q-
  ---------------------------------
  δ ⊑ qe ⋀ C; τ  --->  [qe/δ](C; τ)

(SUBST-NEG-TOP)
  δ ∉ lftv(C)   V(δ,τ) ⊑ Q-
  -------------------------
  C; τ  --->  [A/δ](C; τ)

(SUBST-POS)
  δ ∉ uftv(C)   V(δ,τ) ⊑ Q+
  -----------------------------------------------------------
  qe₁ ⊑ δ ⋀ ... ⋀ qeⱼ ⊑ δ ⋀ C; τ  --->  [qe₁⊔...⊔qeⱼ/δ](C; τ)

(SUBST-INV)
  δ ∉ uftv(C)   V(δ,τ) = Q=   δ' fresh
  --------------------------------------------------------------
  qe₀ ⊑ δ ⋀ ... ⋀ qeⱼ ⊑ δ ⋀ C; τ  --->  [δ'⊔qe₀⊔...⊔qeⱼ/δ](C; τ)

Substitute for contravariant qualifier variables by adding these lossy
rewrites:

(SUBST-NEG-LOSSY)
  δ ∉ lftv(C)   V(δ,τ) = Q-
  -----------------------------------------------
  δ ⊑ q₁ βs₁ ⋀ ... ⋀ δ ⊑ qⱼ βsⱼ ⋀ C; τ
    --->  [(q₁⊓...⊓qⱼ) (βs₁ ∩ ... ∩ βsⱼ)/δ](C; τ)

Run SAT as below for anything we missed.  Then, add bounds:

(BOUND)
  α ∉ lftv(C)   V(α,τ) ∈ { -, +, =, Q= }   q = q₁⊓...⊓qⱼ
  ------------------------------------------------------
  α ⊑ q₁ βs₁ ⋀ ... ⋀ α ⊑ qⱼ βsⱼ ⋀ C; τ
    ---> [U/α]C; ∀α:q. τ


We convert it to SAT as follows:

  Define:

    πa(Q) = A ⊑ Q
    πa(β) = 2 * tvId β + 1
    πa(q1 ⊔ q2) = πa(q1) ⋁ πa(q2)
    πa(q1 ⊓ q2) = πa(q1) ⋀ πa(q2)

    Then given the constraint

      q1 ⊑ q1' ⋀ ... ⋀ qk ⊑ qk'

    generate the formula:

      (πa(q1) ⇒ πa(q1'))
        ⋀ ... ⋀
      (πa(qk) ⇒ πa(qk'))

-}

-- | Represents the meet of several qualifier expressions, which happens
--   when some variable has multiple upper bounds.  These are normalized
--   to implement COMBINE-QLIT and COMBINE-LE.
newtype QEMeet tv = QEMeet { unQEMeet ∷ [S.Set tv] }

instance Bounded (QEMeet tv) where
  minBound = QEMeet [S.empty]
  maxBound = QEMeet []

instance Tv tv ⇒ Ppr.Ppr (QEMeet tv) where
  ppr (QEMeet [])   = Ppr.char 'A'
  ppr (QEMeet [qe]) = Ppr.ppr (QeU qe)
  ppr (QEMeet qem)  =
    Ppr.prec Ppr.precCaret $
      Ppr.fsep (Ppr.punctuate (Ppr.text " ⋀")
                              (Ppr.ppr <$> QeU <$> qem))

instance Tv tv ⇒ Show (QEMeet tv) where showsPrec = Ppr.showFromPpr

instance Ord tv ⇒ Ftv (QEMeet tv) tv where
  ftvTree = FTBranch . map FTSingle . S.toList . ftvSet
  ftvSet  = S.unions . unQEMeet

instance Ord tv ⇒ Monoid (QEMeet tv) where
  mempty  = maxBound
  mappend = foldr (qemInsert . QeU) <$.> unQEMeet

qemSingleton ∷ QExp tv → QEMeet tv
qemSingleton QeA      = maxBound
qemSingleton (QeU αs) = QEMeet [αs]

qemInsert ∷ Ord tv ⇒ QExp tv → QEMeet tv → QEMeet tv
qemInsert qe (QEMeet qem) = QEMeet (loop qe qem) where
  loop QeA      qem = qem
  loop (QeU αs) qem = loopU αs qem
  loopU αs      []       = [αs]
  loopU αs      (βs:qem)
    | αs `S.isSubsetOf` βs = loopU αs qem
    | βs `S.isSubsetOf` αs = βs:qem
    | otherwise            = βs:loopU αs qem

-- | State of the qualifier constraint solver
data QCState tv
  = QCState {
      -- | Generalization candidates, which are type variables that
      --   appear in the qualifier constraint or type-to-be-generalized,
      --   but not in the shape constraint or environment
      sq_αs    ∷ !(S.Set tv),
      -- | The current type to be generalized
      sq_τ     ∷ !(Type tv),
      -- | Free type variables and variances in the type-to-be-generalized.
      sq_τftv  ∷ !(VarMap tv),
      -- | Part of the qualifier constraint: joins of type variables
      --   lower-bounded by qualifier literals.
      sq_βlst  ∷ ![(QLit, S.Set tv)],
      -- | Part of the qualifier constraint: type variables
      --   upper-bounded by (meets of) qualifier expressions.
      sq_vmap  ∷ !(M.Map tv (QEMeet tv))
    }
  deriving Show

instance Tv tv ⇒ Ppr.Ppr (QCState tv) where
  ppr sq = p . M.fromList $
    [ ("αs",    p (sq_αs sq))
    , ("τ",     p (sq_τ sq))
    , ("τftv",  p (sq_τftv sq))
    , ("βlst",  Ppr.fsep . Ppr.punctuate (Ppr.text " ⋀") $
                  [ p ql Ppr.<> Ppr.char '⊑' Ppr.<>
                    Ppr.hcat (Ppr.punctuate (Ppr.char '⊔')
                                (p <$> S.toList tvs))
                  | (ql, tvs) ← sq_βlst sq ])
    , ("vmap",  Ppr.fsep . Ppr.punctuate (Ppr.text " ⋀") $
                  [ p α Ppr.<> Ppr.char '⊑' Ppr.<> p qe
                  | (α, qem) ← M.toList (sq_vmap sq)
                  , qe       ← unQEMeet qem ])
    ]
    where p x = Ppr.ppr x

-- | Solver for qualifier contraints.
--   Given a qualifier constraint, solve and produce type variable
--   bounds.  Also return any remaining inequalities (which must be
--   satisfiable, but we haven't guessed how to satisfy them yet).
solveQualifiers
  ∷ MonadConstraint tv r m ⇒
    -- | Are we generalizing the type of a non-expansive term?
    Bool →
    -- | Generalization candidates
    S.Set tv →
    -- | The constraint as pairs of types in the subqualifier relation
    [(Type tv, Type tv)] →
    -- | The type to be generalized
    Type tv →
    m ([(Type tv, Type tv)], [(tv, QLit)], Type tv)
solveQualifiers value αs qc τ = do
  traceN 3 (TraceIn ("solveQ", "init", αs, qc))
  -- Clean up the constraint, standardize types to qualifier form, and
  -- deal with trivial stuff right away:
  qc             ← stdize qc
  traceN 4 ("solveQ", "stdize", qc)
  -- Decompose implements DECOMPOSE, TOP-SAT, BOT-SAT, and BOT-UNSAT.
  τftv           ← ftvV <$> subst τ
  state          ← decompose qc QCState {
                     sq_αs   = αs,
                     sq_τftv = τftv,
                     sq_βlst = [],
                     sq_vmap = M.empty,
                     sq_τ    = τ
                   }
  traceN 4 ("solveQ", "decompose", state)
  -- Rewrite until it stops changing
  state          ← iterChanging
                     (stdizeType        >=>
                      forceU            >=>
                      substNeg False    >=>!
                      substPosInv       >=>!
                      substNeg True)
                     state
  traceN 4 ("solveQ", "rewrites", state)
  -- Try the SAT solver, then recheck
  state          ← runSat state True
  traceN 4 ("solveQ", "sat", state)
  runSat state False
  -- Finish by reconstructing the constraint and returning the bounds
  -- for the variables to quantify.
  state          ← genVars state
  traceN 3 (TraceOut ("solveQ", "done", state))
  return (recompose state, getBounds state, τ)
  where
  --
  -- Given a list of qualifier inequalities on types, produce a list of
  -- inequalities on standard-form qualifiers, omitting trivial
  -- inequalities along the way.
  stdize qc = mapM each qc where
    each (τl, τh) = do
      qe1 ← makeQExp τl
      qe2 ← makeQExp τh
      return (qe1, qe2)
  --
  -- Given a list of inequalities on qualifiers, rewrite them into
  -- the two decomposed forms:
  --
  --  • γ ⊑ q βs
  --
  --  • q ⊑ βs
  --
  -- This implements DECOMPOSE, BOT-SAT, TOP-SAT, and BOT-UNSAT.
  decompose qc state0 = foldM each state0 qc where
    each state (_,       QeA)     = return state -- (TOP-SAT)
    each state (QeA,     QeU γs2) = each' state (Qa, S.empty) γs2
    each state (QeU γs1, QeU γs2) = each' state (Qu, γs1)     γs2
    each' state (q1, γs1) γs2 = do
      let γs'  = γs1 S.\\ γs2
          βs'  = S.filter flex γs2
          flex = (||) <$> unifiable state <*> (`S.notMember` sq_αs state)
      fβlst ← case q1 of
        -- (BOT-SAT)
        Qu → return id
        -- (BOT-UNSAT)
        _  | S.null βs' → do
               tErrExp_
                 [msg| Qualifier inequality unsatisfiable. |]
                 (pprMsg q1)
                 (pprMsg (QeU γs2))
               return id
           | otherwise →
               return ((q1, βs') :)
      let fvmap = M.unionWith mappend (setToMapWith bound γs')
          bound γ
            | M.lookup γ (sq_τftv state) == Just Covariant
            , γ `S.member` sq_αs state
                                = qemSingleton maxBound
            | unifiable state γ = qemSingleton (QeU γs2)
            | otherwise         = qemSingleton (QeU βs')
      return state {
               sq_βlst = fβlst (sq_βlst state),
               sq_vmap = fvmap (sq_vmap state)
             }
  --
  -- Standardize the qualifiers in the type
  stdizeType state = do
    τ    ← subst τ
    let meet (QEMeet [αs])
          | S.null αs      = Qu
        meet _             = Qa
        qm   = meet <$> sq_vmap state
        τ'   = standardizeQuals qm τ
        τftv = ftvV τ'
    traceN 5 ("stdizeType", τ, τ', qm)
    return state {
             sq_τ    = τ',
             sq_τftv = τftv
           }
  --
  -- Substitute U for qualifier variables upper bounded by U (FORCE-U).
  forceU state =
    substs "forceU" state $
      minBound <$
        M.filterWithKey
          (\β qem → case qem of
            QEMeet [γs] → unifiable state β && S.null γs
            _           → False)
          (sq_vmap state)
  --
  -- Replace Q- or 0 variables by a single upper bound, if they have only
  -- one (SUBST-NEG), or by A if they have none (SUBST-NEG-TOP).  If
  -- 'doLossy', then we include SUBST-NEG-LOSSY as well, which uses
  -- approximate lower bounds for combining multiple upper bounds.
  substNeg doLossy state =
    substs who state $ M.fromDistinctAscList $ do
      δ ← S.toAscList (sq_αs state)
      guard (unifiable state δ
             && M.lookup δ (sq_τftv state) ⊑ Just QContravariant)
      case M.lookup δ (sq_vmap state) of
        Nothing            → return (δ, maxBound)
        Just (QEMeet [])   → return (δ, maxBound)
        Just (QEMeet [qe]) → return (δ, QeU qe)
        Just (QEMeet qes)
          | doLossy        → return (δ, bigMeet (QeU <$> qes))
          | otherwise      → mzero
    where who = if doLossy then "substNeg/lossy" else "substNeg"
  --
  -- Replace Q+ and Q= variables with tight lower bounds.
  substPosInv state = do
    let add qe (S.toList → [β])
          | β `S.member` sq_αs state
          = M.insertWith (liftA2 (⊔)) β (Just qe)
        add _  βs
          = M.union (setToMap Nothing βs)
        -- For each (γ ⊑ meet) in the state, make γ ⊑ each qe in the meet
        add_vmap = M.foldrWithKey each <-> (sq_vmap state) where
          each γ (QEMeet qem) = foldr (add (qvarexp γ)) <-> qem
        -- for each (q ⊑ βs) in the state, make q ⊑ βs
        add_βlst = foldr each <-> sq_βlst state where
          each (q, βs) = add (qlitexp q) βs
        -- The lower bounds
        lbs = M.mapMaybe id . add_βlst . add_vmap
            $ setToMap (Just minBound)
                       (S.filter (unifiable state) (sq_αs state))
                M.\\ sq_vmap state
        -- Positive variables with lower bounds
        pos  = lbs M.\\ M.filter (/= QCovariant) (sq_τftv state)
        -- Invariant variables with lower bounds
        inv  = lbs `M.intersection`
                 M.filter (== QInvariant) (sq_τftv state)
    (δ's, inv) ← first S.fromDistinctAscList . unzip <$> sequence
      [ do
          δ' ← newTV' KdQual
          return (δ', (δ, S.insert δ' `mapQExp` qe))
      | (δ, qe) ← M.toAscList inv
      , qe /= minBound ]
    substs "substPosInv"
           state {
             sq_αs = sq_αs state `S.union` δ's
           }
           (pos `M.union` M.fromDistinctAscList inv)
  --
  -- Given a list of type variables and qualifiers, substitute for each,
  -- updating the state as necessary.
  substs ∷ MonadConstraint tv r m ⇒
           String → QCState tv → M.Map tv (QExp tv) → m (QCState tv)
  substs who state γqes0
    | M.null γqes0 = return state
    | otherwise      = do
    traceN 4 (who, γqes0, state)
    let sanitize _    []  []
          = typeBug "subst" $
              "Attempted impossible substitution: " ++ show γqes0
        sanitize _    acc []
          = unsafeSubsts state (M.fromDistinctAscList (reverse acc))
        sanitize seen acc ((γ, qe):rest)
          | S.member γ (S.union seen (ftvSet qe))
          = sanitize seen acc rest
          | otherwise
          = sanitize (seen `S.union` ftvSet qe) ((γ, qe):acc) rest
    sanitize S.empty [] (M.toAscList γqes0)
  --
  -- This does the main work of substitution, and it has a funny
  -- precondition (which is enforced by 'subst', above), namely:
  -- the type variables will be substituted in increasing order, so the
  -- image of later variables must not contain earlier variables.
  --
  -- This is okay:     { 1 ↦ 2 3, 2 ↦ 4 }
  -- This is not okay: { 1 ↦ 3 4, 2 ↦ 1 }
  unsafeSubsts state γqes = do
    sequence [ do
                 let τ = qualToType (liftVQExp qe)
                 writeTV γ τ
                 updatePinnedTVs γ τ
             | (γ, qe) ← M.toList γqes ]
    let γset          = M.keysSet γqes
        unchanged set = S.null (γset `S.intersection` set)
        (βlst, βlst') = List.partition (unchanged . snd) (sq_βlst state)
        (vmap, vmap') = M.partitionWithKey
                          (curry (unchanged . ftvSet))
                          (sq_vmap state)
    ineqs ← stdize $
      [ (qualToType ql, qualToType βs)
      | (ql, βs) ← βlst' ]
        ++
      [ (fvTy γ, qualToType qe)
      | (γ, qem) ← M.toList vmap'
      , qe       ← unQEMeet qem ]
    state ← decompose ineqs
      state {
        sq_αs   = sq_αs state S.\\ γset,
        sq_τftv = M.foldrWithKey substQE (sq_τftv state) γqes,
        sq_βlst = βlst,
        sq_vmap = vmap
      }
    traceN 4 ("subst", γqes, state)
    return state
  --
  -- As a last ditch effort, use a simple SAT solver to find a
  -- decent literal-only substitution.
  runSat state doIt = do
    let formula = toSat state
        sols    = SAT.solve =<< SAT.assertTrue formula SAT.newSatSolver
    traceN 4 ("runSat", formula, sols)
    case sols of
      []  → do
        typeError_ [msg| Qualifier constraints unsatisfiable |]
        return state
      sat:_ | doIt
          → substs "sat" state =<<
              M.fromDistinctAscList <$> sequence
                [ return (δ, qlitexp ql)
                  -- warn $ "\nSAT: substituting " ++ show (QE ql slack) ++
                  --        " for type variable " ++ show δ
                | δ ← S.toAscList (sq_αs state)
                , unifiable state δ
                , let (ql, var) = decodeSatVar δ (sq_τftv state) sat
                , ql == Qa || var /= QInvariant ]
      _   → return state
  --
  toSat state = foldr (SAT.:&&:) SAT.Yes $
      [ (πa τftv q ==> πa τftv βs)
      | (q, βs) ← sq_βlst state ]
    ++
      [ (πa τftv (Free α) ==> πa τftv αs)
      | (α, QEMeet qes) ← M.toList (sq_vmap state)
      , unifiable state α
      , αs              ← qes ]
    where
      p ==> q = SAT.Not p SAT.:||: q
      τftv    = sq_τftv state
  --
  -- Find the variables to generalize
  genVars state = return state { sq_αs = αs' } where
    αs'  = sq_αs state `S.intersection` kset
    kset = M.keysSet (keep (sq_τftv state))
    keep = if value then id else M.filter (`elem` [-2,-1,1,2])
  --
  -- Find the the bounds of variables to generalize
  getBounds state =
    map (id &&& getBound) (S.toList (sq_αs state)) where
      getBound α = maybe maxBound qeMeetQLit (M.lookup α (sq_vmap state))
  --
  -- The QLit lower bound of a QExp
  qeMeetQLit (QEMeet []) = maxBound
  qeMeetQLit _           = minBound
  --
  -- Turn the decomposed constraint back into a list of pairs of types.
  recompose state =
      [ (fvTy γ, clean βs)
      | (γ, QEMeet qem) ← M.toList (sq_vmap state)
      , γ `S.notMember` sq_αs state
      , βs ← qem ]
    ++
      [ (qualToType ql, clean βs)
      | (ql, βs) ← sq_βlst state ]
    where
    clean βs = qualToType (βs S.\\ sq_αs state)
  --
  makeQExp τ = do
    qe ← qualifier <$> subst τ
    case qe of
      QeA    → return QeA
      QeU γs → do
        (γs', qls) ← partitionJust tvQual <$> mapM fromVar (S.toAscList γs)
        if any (== Qa) qls
          then return QeA
          else return (QeU (S.fromDistinctAscList γs'))
  --
  fromVar (Free α) = return α
  fromVar _        = typeBug "solveQualifiers" "Got bound type variable"
  --
  unifiable _ α = tvKindIs KdQual α

-- | Update a type variable variance map as a result of substituting a
--   qualifier expression for a type variable.
substQE ∷ Ord tv ⇒ tv → QExp tv → VarMap tv → VarMap tv
substQE β qe vmap = case takeMap β vmap of
  (Just v, vmap') → M.unionWith (⊔) vmap' (setToMap v (ftvSet qe))
  _               → vmap

-- | Lookup a key in a map and remove the key from the map.
takeMap ∷ Ord k ⇒ k → M.Map k v → (Maybe v, M.Map k v)
takeMap = M.updateLookupWithKey (\_ _ → Nothing)

-- | Lift a 'S.Set' to a 'M.Map' with constant value
setToMap   ∷ a → S.Set k → M.Map k a
setToMap   = setToMapWith . const

-- | Lift a 'S.Set' to a 'M.Map' with values computed from keys.
setToMapWith   ∷ (k → a) → S.Set k → M.Map k a
setToMapWith f = M.fromDistinctAscList . map (id &&& f) . S.toAscList

---
--- SAT SOLVING FOR QUALIFIER CONSTRAINTS
---

-- | To encode some qualifier as a SAT formula
class SATable a v where
  πa ∷ VarMap v → a → SAT.Boolean

instance SATable QLit v where
  πa _ Qa = SAT.Yes
  πa _ _  = SAT.No

instance Tv v ⇒ SATable (TyVar v) v where
  πa vm (Free β) = encodeSatVar β vm
  πa _  _        = SAT.No

instance Tv v ⇒ SATable (S.Set v) v where
  πa vm vs = S.fold ((SAT.:||:) . πa vm . Free) SAT.No vs

-- | Given a type variable and a SAT solution, return a bound
--   for that type variable as implied by the solution.
decodeSatVar ∷ Tv tv ⇒ tv → VarMap tv → SAT.SatSolver → (QLit, Variance)
decodeSatVar β vm solver = (q, var) where
  (maximize, var) = maximizeVariance β vm
  q   = case (maximize, mba) of
    -- For minimizing variables, each component tells us whether that
    -- component may be omitted from the substitution, so we choose the
    -- smallest qualifier literal that includes the required components.
    (False, Just False) → Qa
    (False, _         ) → Qu
    -- For maximizing variables, each component tells us whether that
    -- component may be included in the substitution, so we choose the
    -- largest qualifier literal that omits the forbidden components.
    (True , Just False) → Qu
    (True , _         ) → Qa
  mba = SAT.lookupVar βa solver
  βa  = tvUniqueID β

-- | Encode the 'q' component of type variable 'β'.  We want to maximize
--   contravariant variables and minimize all the others.  Since the
--   solver tries true before false, we use a positive literal to stand
--   for the 'q' component of a maximized variable and a negative
--   literal for a minimized variable.
encodeSatVar ∷ Tv tv ⇒ tv → VarMap tv → SAT.Boolean
encodeSatVar β vm
  | fst (maximizeVariance β vm) = SAT.Var z
  | otherwise                   = SAT.Not (SAT.Var z)
  where z = tvUniqueID β

maximizeVariance ∷ Ord tv ⇒ tv → VarMap tv → (Bool, Variance)
maximizeVariance γ vm = case M.findWithDefault 0 γ vm of
  v@QCovariant  → (False, v)
  v@QInvariant  → (False, v)
  v             → (True,  v)

instance Ppr.Ppr SAT.Boolean where pprPrec = Ppr.pprFromShow
instance Ppr.Ppr SAT.SatSolver where pprPrec = Ppr.pprFromShow


{-

OPTIMIZATIONS FROM SIMONET 2003

6.1 Collapsing Cycles

  This is the SCC phase

6.2 Polarities (implemented in buildGraph)

  Upper bounds on positive variables and lower bounds on negative
  variables are irrelevant, e.g.:

    f : ∀ α ≤ A. 1 → α × α
    f : ∀ α. 1 → α × α

  Or:

    let rec f = λx. f (f x) in f
    f : α → β [β ≤ α]
    f : ∀α. ∀β ≤ α. α → β
    f : ∀α. ∀β. α → β

6.3 Reducing Chains (implemented in polarizedReduce)

  A positive variable with a single predecessor can be fused with the
  predecessor; dually, a negative variable can be fused with a single
  successor.

    ∀ α ≤ A. α → 1
    A → 1

    ∀ α ≤ A. α × α → 1
    A × A → 1

  Currently this is implemented only for variables that occur only once.
  Why?

6.4 Polarized Garbage Collection

  ?

6.5 Minimization

  If two positive variables have all the same predecessors, the can be
  coalesced. Dually for negative variables with the same successors.

  ∀ α ≤ C. ∀ β ≤ C. α × β → 1
    A × B → 1

  ∀ α ≤ C. α × α → 1
    C × C → 1
    A × B → 1
-}

