{-#
  LANGUAGE
    FlexibleInstances,
    FunctionalDependencies,
    MultiParamTypeClasses,
    UndecidableInstances,
    UnicodeSyntax,
    ViewPatterns
  #-}
module Statics.Constraint (
  MonadConstraint(..),
  generalize, generalizeList, generalizeEx,
{-
  mapConstraintT, runConstraintT,
  generalize, generalizeList, generalizeEx,
  -}
) where

import Util
import Data.Loc (bogus)
import ErrorMessage
import Type

{-
-- From fgs:
import Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Graph   as Gr

-- From incremental-sat-solver
import qualified Data.Boolean.SatSolver as SAT

import Syntax
import TV
import MonadRef
import Util
import Ppr
import Rank (Rank)
import qualified UnionFind as UF

import qualified Data.List  as List
import qualified Data.Map   as M
import qualified Text.PrettyPrint as Ppr
-}

import Prelude ()
import qualified Data.Set   as S

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
  -- | Update the pinned TVs list to reflect a substitution.
  --   PRECONDITION: @τ@ is fully substituted
  updatePinnedTVs ∷ tv → Type tv → m ()
  --
  -- | Figure out which variables to generalize in a piece of syntax.
  --   The 'Bool' indicates whether the syntax whose type is being
  --   generalized is a syntactic value.  Returns a list of
  --   generalizable variables and their qualifier bounds.
  generalize'     ∷ Bool → Rank → Type tv → m [(tv, QLit)]
  --
  -- | Return a string representation of the constraint
  showConstraint  ∷ m String

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

constraintBug ∷ MonadSubst tv r m ⇒ String → String → m a
constraintBug = throwAlms <$$> almsBug StaticsPhase bogus

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
      Nothing → constraintBug "generalizeEx"
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

{-
---
--- Eager subtyping constraint solver
---

-- | Constraint monad transformer adds constraint solver state.
newtype ConstraintT tv r m a
  = ConstraintT {
      unConstraintT_ ∷ StateT (CTState tv r) m a
    }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadTrace)

-- | The state of the constraint solver.
data CTState tv r
  = CTState {
      -- | Graph for subtype constraints on type variables and atomic
      --   type constructors
      csGraph   ∷ !(Gr tv ()),
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

instance Tv tv ⇒ Ppr (CTState tv r) where
  ppr cs = ppr . M.fromList $
    [ ("graph",    Ppr.fsep . Ppr.punctuate Ppr.comma $
                     [ pprPrec 10 α1
                         Ppr.<> Ppr.text "<:"
                         Ppr.<> pprPrec 10 α2
                     | (α1, α2) ← Gr.labNodeEdges (csGraph cs) ])
    , ("quals",    Ppr.fsep . Ppr.punctuate Ppr.comma $
                     [ pprPrec 9 τ1
                         Ppr.<> Ppr.char '⊑'
                         Ppr.<> pprPrec 9 τ2
                     | (τ1, τ2) ← csQuals cs ])
    ]

mapConstraintT   ∷ (∀s. m (a, s) → n (b, s)) →
                   ConstraintT tv r m a → ConstraintT tv r n b
mapConstraintT f = ConstraintT . mapStateT f . unConstraintT_

-- | Run the constraint solver, starting with an empty (true)
--   constraint.  Seeds the atom graph with the type constructors that
--   are involved in the subtyping order.
runConstraintT ∷ MonadSubst tv r m ⇒ ConstraintT tv r m a → m a
runConstraintT m = evalStateT (unConstraintT_ m) cs0
  where cs0        = CTState {
                       csGraph   = Gr.empty,
                       csNodeMap = Gr.new,
                       csEquivs  = M.empty,
                       csQuals   = [],
                       csPinned  = []
                     }

-- | Pass through for reference operations
instance MonadRef r m ⇒ MonadRef r (ConstraintT tv r m) where
  newRef        = lift <$> newRef
  readRef       = lift <$> readRef
  writeRef      = lift <$$> writeRef

-- | Pass through for unification operations
instance MonadSubst tv r m ⇒ MonadSubst tv r (ConstraintT tv r m) where
  newTV_ (Universal, kind, bound, descr) = do
    α ← lift (newTV' (kind, descr))
    fvTy α ⊏: bound
    return α
  newTV_ attrs  = lift (newTV' attrs)
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  collectTV     = mapConstraintT (mapListen2 collectTV)
  reportTV      = lift . reportTV
  monitorChange = mapConstraintT (mapListen2 monitorChange)
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  setChanged    = lift setChanged

instance MonadSubst tv r m ⇒ MonadReadTV tv (ConstraintT tv r m) where
  readTV = lift . readTV

-- | 'ConstraintT' implements 'Graph'/'NodeMap' transformer operations
--   for accessing its graph and node map.
instance (Ord tv, Monad m) ⇒
         Gr.MonadNM tv () Gr (ConstraintT tv r m) where
  getNMState = ConstraintT (gets (csNodeMap &&& csGraph))
  getNodeMap = ConstraintT (gets csNodeMap)
  getGraph   = ConstraintT (gets csGraph)
  putNMState (nm, g) = ConstraintT . modify $ \cs →
    cs { csNodeMap = nm, csGraph = g }
  putNodeMap nm = ConstraintT . modify $ \cs → cs { csNodeMap = nm }
  putGraph g    = ConstraintT . modify $ \cs → cs { csGraph = g }

-- | Constraint solver implementation.
instance MonadSubst tv r m ⇒ MonadConstraint tv r (ConstraintT tv r m) where
  τ <: τ' = do
    traceN 3 ("<:", τ, τ')
    runSeenT (subtypeTypes False τ τ')
  τ =: τ' = do
    traceN 3 ("=:", τ, τ')
    runSeenT (subtypeTypes True τ τ')
  τ ⊏: τ' = do
    traceN 3 ("⊏:", toQualifierType τ, toQualifierType τ')
    ConstraintT . modify . csQualsUpdate $
      ((toQualifierType τ, toQualifierType τ') :)
  --
  getPinnedTVs      = S.unions <$> ConstraintT (gets csPinned)
  --
  withPinnedTVs a m = do
    αs     ← ftvSet a
    ConstraintT (modify (csPinnedUpdate (αs :)))
    result ← m
    ConstraintT (modify (csPinnedUpdate tail))
    return result
  --
  updatePinnedTVs α τ = do
    let βs      = M.keysSet (ftvPure τ)
        update  = snd . mapAccumR eachSet False
        eachSet False set
          | α `S.member` set = (True, βs `S.union` S.delete α set)
        eachSet done set       = (done, set)
    ConstraintT (modify (csPinnedUpdate update))
  --
  generalize'    = solveConstraint
  saveConstraint = do
    c      ← ConstraintT get
    return . ConstraintT $ do
      pinned ← gets csPinned
      put (csPinnedUpdate (`asLengthOf` pinned) c)
    where
    xs `asLengthOf` ys =
      reverse (zipWith const
                       (reverse xs ++ repeat S.empty)
                       (reverse ys))
  showConstraint = show <$> ConstraintT get

-- | Monad transformer for tracking which type comparisons we've seen,
--   in order to implement recursive subtyping.  A pair of types mapped
--   to @True@ means that they're known to be equal, whereas @False@
--   means that their only known to be subtyped.
type SeenT tv r m = StateT (M.Map (REC_TYPE tv, REC_TYPE tv) Bool)
                           (ConstraintT tv r m)

-- | Run a recursive subtyping computation.
runSeenT ∷ MonadSubst tv r m ⇒ SeenT tv r m a → ConstraintT tv r m a
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
subtypeTypes unify τ10 τ20 = do
  check τ10 τ20
  where
  check τ1 τ2 = do
    lift $ gtraceN 4 ("subtypeTypes", unify, τ1, τ2)
    τ1'  ← substDeep τ1
    τ2'  ← substDeep τ2
    seen ← get
    if M.lookup (REC_TYPE τ1', REC_TYPE τ2') seen >= Just unify
      then do
        let ps = [ p | p ← M.keys seen, p == (REC_TYPE τ1', REC_TYPE τ2') ]
        traceN 5 ("found!", τ1', τ2', ps, unify)
      else do
        put (M.insert (REC_TYPE τ1', REC_TYPE τ2') unify seen)
        decomp τ1' τ2'
  --
  decomp τ1 τ2 = case (τ1, τ2) of
    (VarTy v1, VarTy v2)
      | v1 == v2 → return ()
    (VarTy (FreeVar r1), VarTy (FreeVar r2))
      | tvFlavorIs Universal r1, tvFlavorIs Universal r2 →
      if unify
        then unifyVar r1 (fvTy r2)
        else do
          lift (makeEquivTVs r1 r2)
          addEdge r1 r2
    (VarTy (FreeVar r1), _)
      | tvFlavorIs Universal r1 → do
      τ2' ← lift $ occursCheck r1 τ2 >>= if unify then return else copyType
      unifyVar r1 τ2'
      unless unify (check τ2' τ2)
    (_, VarTy (FreeVar r2))
      | tvFlavorIs Universal r2 → do
      τ1' ← lift $ occursCheck r2 τ1 >>= if unify then return else copyType
      unifyVar r2 τ1'
      unless unify (check τ1 τ1')
    (QuaTy TyQu αs1 τ1', QuaTy TyQu αs2 τ2')
      | if unify
          then αs1 == αs2
          else length αs1 == length αs2
            && and (zipWith ((⊒)`on`snd) αs1 αs2) →
      check τ1' τ2'
    (QuaTy ExQu αs1 τ1', QuaTy ExQu αs2 τ2')
      | αs1 == αs2 →
      check τ1' τ2'
    (ConTy c1 τs1, ConTy c2 τs2)
      | c1 == c2 && length τs1 == length τs2 →
      sequence_
        [ if unify
            then if isQVariance var
              then τ1' ~: τ2'
              else check τ1' τ2'
            else relateTypes var τ1' τ2'
        | var ← getVariances c1 (length τs1)
        | τ1' ← τs1
        | τ2' ← τs2 ]
    (RowTy n1 τ11 τ12, RowTy n2 τ21 τ22)
      | n1 == n2 → do
        check τ11 τ21
        check τ12 τ22
      | otherwise   → do
        α ← newTVTy
        check (RowTy n1 τ11 α) τ22
        β ← newTVTy
        check τ12 (RowTy n2 τ21 β)
        check α β
    (RecTy _ τ1', _) →
      decomp (openTy 0 [τ1] τ1') τ2
    (_, RecTy _ τ2') →
      decomp τ1 (openTy 0 [τ2] τ2')
    _ →
      fail $ "Type error: type ‘" ++ show τ1 ++ "’ " ++
             (if unify
                then "cannot be unified with"
                else "is not a subtype of") ++
             " ‘" ++ show τ2 ++ "’"
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
   foldTypeM (mkQuaF (return <$$$> QuaTy))
             (mkBvF (return <$$$> bvTy))
             fvar
             fcon
             (return <$$$> RowTy)
             (mkRecF (return <$$> RecTy))
  where
    fvar α | tvFlavorIs Universal α = newTVTy' (tvKind α)
           | otherwise              = return (fvTy α)
    -- Nullary type constructors that are involved in the atomic subtype
    -- relation are converted to type variables:
    fcon c τs
      = ConTy c <$> sequence
          [ -- A Q-variant type constructor parameter becomes a single
            -- type variable:
            if isQVariance var
              then newTVTy' QualKd
              else return τ
          | τ   ← τs
          | var ← getVariances c (length τs) ]

-- | Unify a type variable with a type, where the type must be locally
--   closed.
--   ASSUMPTIONS: @α@ has not been substituted and the occurs check has
--   already passed.
unifyVar ∷ MonadSubst tv r m ⇒ tv → Type tv → SeenT tv r m ()
unifyVar α τ0 = do
  lift $ gtraceN 4 ("unifyVar", α, τ0)
  τ ← substDeep τ0
  unless (lcTy 0 τ) $
    fail $ "Type error: Cannot unify because insufficiently polymorphic"
  writeTV α τ
  updatePinnedTVs α τ
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
occursCheck ∷ MonadSubst tv r m ⇒ tv → Type tv → ConstraintT tv r m (Type tv)
occursCheck α τ = do
  gtraceN 3 ("occursCheck", α, τ)
  (guarded, unguarded) ← (M.keys***M.keys) . M.partition id <$> ftvG τ
  whenM (anyA (checkEquivTVs α) unguarded) $
    fail $ "Type error: Occurs check failed: cannot construct infinite " ++ 
           "type such that " ++ show α ++ " = " ++ show τ
  recVars ← filterM (checkEquivTVs α) guarded
  when (not (null recVars)) $ gtraceN 3 ("occursCheck", "recvars", recVars)
  return (foldr closeRec τ recVars)

-- | Records that two type variables have the same size.
makeEquivTVs  ∷ MonadSubst tv r m ⇒ tv → tv → ConstraintT tv r m ()
makeEquivTVs α β = do
  pα ← getTVProxy α
  pβ ← getTVProxy β
  UF.coalesce_ (return <$$> S.union) pα pβ

-- | Checks whether two type variables have the same size.
checkEquivTVs ∷ MonadSubst tv r m ⇒ tv → tv → ConstraintT tv r m Bool
checkEquivTVs α β = do
  pα ← getTVProxy α
  pβ ← getTVProxy β
  UF.sameRepr pα pβ

-- | Clears all size-equivalence classes and rebuilds them based on the
--   current atomic subtyping constraint graph.
resetEquivTVs ∷ MonadSubst tv r m ⇒ ConstraintT tv r m ()
resetEquivTVs = do
  ConstraintT (modify (csEquivsUpdate (const M.empty)))
  g     ← Gr.getGraph
  mapM_ (uncurry makeEquivTVs)
        [ (α, β) | (α, β) ← Gr.labNodeEdges g ]

-- | Helper to get the proxy the represents the size-equivalence class
--   of a type variable.
getTVProxy ∷ MonadSubst tv r m ⇒ tv → ConstraintT tv r m (TVProxy tv r)
getTVProxy α = do
  equivs ← ConstraintT (gets csEquivs)
  case M.lookup α equivs of
    Just pα → return pα
    Nothing → do
      pα ← UF.create (S.singleton α)
      ConstraintT (modify (csEquivsUpdate (M.insert α pα)))
      return pα

--- CONSTRAINT SOLVING

-- | Solve a constraint as much as possible, returning the type
--   variables to generalize and their qualifier bounds.
solveConstraint ∷ MonadSubst tv r m ⇒
                  Bool → Rank → Type tv → ConstraintT tv r m ([tv], [QLit])
solveConstraint value γrank τ = do
  τftv ← ftvV τ;
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
  qc    ← ConstraintT (gets csQuals)
  cftv  ← ftvSet . map snd =<< Gr.getsGraph Gr.labNodes
  qcftv ← ftvSet qc
  αs    ← S.fromDistinctAscList <$>
            filter (tvFlavorIs Universal) <$>
              (removeByRank γrank <$>
                S.toAscList $
                  (qcftv `S.union` M.keysSet τftv) S.\\ cftv)
  (qc, αqs, τ) ← solveQualifiers value αs qc τ
  ConstraintT (modify (csQualsUpdate (const qc)))
  gtraceN 2 (TraceOut ("gen", "finished", αqs, τ))
  resetEquivTVs
  return (map fst αqs, map snd αqs)
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
          β ← newTVTy' QualKd
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
    coalesceList _      [] = fail "BUG! coalesceList got []"
    -- Assign n2 to n1, updating the graph, type variables, and ftvs,
    -- and return whichever node survives
    coalesce (n1, α1) (n2, α2) τftv = do
      ftv2 ← ftvSet α2
      if α1 `S.member` ftv2
        then return ((n2, α2), τftv)
        else do
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

gtraceN ∷ (MonadSubst tv r m, TraceMessage a) ⇒ Int → a → ConstraintT tv r m ()
gtraceN =
  if debug then \n info →
    if n <= debugLevel then do
      trace info
      cs ← ConstraintT get
      let doc = ppr cs
      unless (Ppr.isEmpty doc) $
        trace (Ppr.nest 4 doc)
    else return ()
  else \_ _ → return ()

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

-- | Internal representation of qualifier expressions used by the
--   qualifier solver.
data QE tv = QE { qeQLit ∷ !QLit, qeQSet ∷ !(S.Set tv) }

instance Tv tv ⇒ Show (QE tv) where
  show (QE A _)  = "A"
  show (QE U γs) = concat (List.intersperse "⊔" (q' γs'))
    where γs' = map (show . tvUniqueID) (S.toList γs)
          q'  = if not (S.null γs) then id else ("U" :)

instance Tv tv ⇒ Ppr (QE tv) where
  pprPrec _ (QE A _)  = Ppr.char 'A'
  pprPrec p (QE U γs) = case items of
    []  → Ppr.char 'U'
    [x] → x
    xs  → parensIf (p > 6) (Ppr.fcat (Ppr.punctuate (Ppr.char '⊔') xs))
    where items = map (Ppr.text . show . tvUniqueID) (S.toList γs)

instance Eq tv ⇒ Eq (QE tv) where
    QE A  _   == QE A  _   = True
    QE q1 γs1 == QE q2 γs2 = q1 == q2 && γs1 == γs2

instance Ord tv ⇒ Ord (QE tv) where
    QE A  _   `compare` QE A  _   = EQ
    QE q1 γs1 `compare` QE q2 γs2
      | q1 == q2  = γs1 `compare` γs2
      | q1 ⊑  q2  = LT
      | otherwise = GT

instance Bounded (QE tv) where
  minBound = QE minBound S.empty
  maxBound = QE maxBound S.empty

instance Ord tv ⇒ Lattice (QE tv) where
  QE A _   ⊔ _        = maxBound
  _        ⊔ QE A _   = maxBound
  QE U γs1 ⊔ QE U γs2 = QE U (γs1 `S.union` γs2)
  --
  QE A _   ⊓ qe2      = qe2
  qe1      ⊓ QE A _   = qe1
  QE U γs1 ⊓ QE U γs2 = QE U (γs1 `S.intersection` γs2)
  --
  _        ⊑ QE A  _  = True
  QE A _   ⊑ _        = False
  QE U γs1 ⊑ QE U γs2 = γs1 `S.isSubsetOf` γs2

instance Qualifier (QE tv) tv where
  toQualifierType (QE q γs) =
    toQualifierType (QExp q (FreeVar <$> S.toList γs))

instance Ord tv ⇒ Ftv (QE tv) tv where
  ftvTree (QE _ γs) = return (FTBranch (map FTSingle (S.toList γs)))

-- | Represents the meet of several qualifier expressions, which happens
--   when some variable has multiple upper bounds.  These are normalized
--   to implement COMBINE-QLIT and COMBINE-LE.
newtype QEMeet tv = QEMeet { unQEMeet ∷ [QE tv] }

instance Bounded (QEMeet tv) where
  minBound = QEMeet [minBound]
  maxBound = QEMeet []

instance Tv tv ⇒ Show (QEMeet tv) where
  show (QEMeet [])  = "A"
  show (QEMeet qem) = concat (List.intersperse " ⊓ " (map show qem))

instance Ord tv ⇒ Ftv (QEMeet tv) tv where
  ftvTree = ftvTree . unQEMeet

instance Ord tv ⇒ Monoid (QEMeet tv) where
  mempty  = maxBound
  mappend = foldr qemInsert <$.> unQEMeet

qemSingleton ∷ QE tv → QEMeet tv
qemSingleton (QE A _) = maxBound
qemSingleton qe       = QEMeet [qe]

qemInsert ∷ Ord tv ⇒ QE tv → QEMeet tv → QEMeet tv
qemInsert qe (QEMeet qem) = QEMeet (loop qe qem) where
  loop (QE A _)       qem = qem
  loop qe             []  = [qe]
  loop (qe@(QE q γs)) (qe'@(QE q' γs'):qem)
    | S.null γs, S.null γs'
                          = loop (QE (q ⊓ q') S.empty) qem
    | qe ⊑ qe'            = loop qe qem
    | qe' ⊑ qe            = qe':qem
    | otherwise           = qe':loop qe qem

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

instance Tv tv ⇒ Ppr (QCState tv) where
  ppr sq = ppr . M.fromList $
    [ ("αs",    ppr (sq_αs sq))
    , ("τ",     ppr (sq_τ sq))
    , ("τftv",  ppr (sq_τftv sq))
    , ("βlst",  Ppr.fsep . Ppr.punctuate (Ppr.text " ⋀") $
                  [ ppr ql Ppr.<> Ppr.char '⊑' Ppr.<>
                    Ppr.hcat (Ppr.punctuate (Ppr.char '⊔')
                                (map ppr (S.toList tvs)))
                  | (ql, tvs) ← sq_βlst sq ])
    , ("vmap",  Ppr.fsep . Ppr.punctuate (Ppr.text " ⋀") $
                  [ ppr α Ppr.<> Ppr.char '⊑' Ppr.<> ppr qe
                  | (α, qem) ← M.toList (sq_vmap sq)
                  , qe       ← unQEMeet qem ])
    ]

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
  τftv           ← ftvV τ
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
  stdize qc = foldM each [] qc where
    each qc' (τl, τh) = do
      qe1 ← makeQE τl
      qe2 ← makeQE τh
      if qe1 ⊑ qe2
        then return qc'
        else return ((qe1, qe2) : qc')
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
    each state (QE q1 γs1, QE q2 γs2) = do
      let γs'  = γs1 S.\\ γs2
          βs'  = S.filter flex γs2
          flex = (||) <$> unifiable state <*> (`S.notMember` sq_αs state)
      fβlst ← case q1 \-\ q2 of
        -- (BOT-SAT)
        U  →   return id
        -- (BOT-UNSAT)
        q' | S.null βs' →
               fail $ "Type error: qualifier inequality unsatisfiable: " ++
                      show (toQualifierType (QE q1 γs1)) ++
                      " ⊑ " ++ show (toQualifierType (QE q2 γs2))
           | otherwise →
               return ((q', βs') :)
      let fvmap = if q2 == maxBound
                    then id     -- (TOP-SAT)
                    else M.unionWith mappend (setToMapWith bound γs')
          bound γ
            | M.lookup γ (sq_τftv state) == Just Covariant
            , γ `S.member` sq_αs state
                                = qemSingleton maxBound
            | unifiable state γ = qemSingleton (QE q2 γs2)
            | otherwise         = qemSingleton (QE q2 βs')
      return state {
               sq_βlst = fβlst (sq_βlst state),
               sq_vmap = fvmap (sq_vmap state)
             }
  --
  -- Standardize the qualifiers in the type
  stdizeType state = do
    τ    ← substDeep τ
    let meet = bigMeet . map qeQLit . filter (S.null . qeQSet) . unQEMeet
        qm   = meet <$> sq_vmap state
        τ'   = standardizeQuals qm τ
    traceN 5 ("stdizeType", τ, τ', qm)
    τftv ← ftvV τ'
    return state {
             sq_τ    = τ',
             sq_τftv = τftv
           }
  --
  -- Substitute U for qualifier variables upper bounded by U (FORCE-U).
  forceU state =
    subst "forceU" state $
      minBound <$
        M.filterWithKey
          (\β qem → case qem of
            QEMeet [QE U γs] → unifiable state β && S.null γs
            _                → False)
          (sq_vmap state)
  --
  -- Replace Q- or 0 variables by a single upper bound, if they have only
  -- one (SUBST-NEG), or by A if they have none (SUBST-NEG-TOP).  If
  -- 'doLossy', then we include SUBST-NEG-LOSSY as well, which uses
  -- approximate lower bounds for combining multiple upper bounds.
  substNeg doLossy state =
    subst who state $ M.fromDistinctAscList $ do
      δ ← S.toAscList (sq_αs state)
      guard (unifiable state δ
             && M.lookup δ (sq_τftv state) ⊑ Just QContravariant)
      case M.lookup δ (sq_vmap state) of
        Nothing            → return (δ, maxBound)
        Just (QEMeet [])   → return (δ, maxBound)
        Just (QEMeet [qe]) → return (δ, qe)
        Just (QEMeet qes)
          | doLossy        → return (δ, bigMeet qes)
          | otherwise      → mzero
    where who = if doLossy then "substNeg/lossy" else "substNeg"
  --
  -- Replace Q+ and Q= variables with tight lower bounds.
  substPosInv state = do
    let add qe (QE U (S.toList → [β]))
          | β `S.member` sq_αs state
          = M.insertWith (liftA2 (⊔)) β (Just qe)
        add _  (QE _ βs)
          = M.union (setToMap Nothing βs)
        lbs0 = setToMap (Just minBound)
                        (S.filter (unifiable state) (sq_αs state))
                 M.\\ sq_vmap state
        lbs1 = M.foldrWithKey each lbs0 (sq_vmap state) where
          each γ (QEMeet qem) = foldr (add (QE U (S.singleton γ))) <-> qem
        lbs2 = M.mapMaybe id (foldr each lbs1 (sq_βlst state)) where
          each (q, βs) = add (QE q S.empty) (QE U βs)
        pos  = lbs2 M.\\ M.filter (/= QCovariant) (sq_τftv state)
        inv  = lbs2 `M.intersection`
                 M.filter (== QInvariant) (sq_τftv state)
    (δ's, inv) ← first S.fromDistinctAscList . unzip <$> sequence
      [ do
          δ' ← newTV' QualKd
          return (δ', (δ, QE q (S.insert δ' βs)))
      | (δ, qe@(QE q βs)) ← M.toAscList inv
      , qe /= minBound ]
    subst "substPosInv"
          state {
            sq_αs = sq_αs state `S.union` δ's
          }
          (pos `M.union` M.fromDistinctAscList inv)
  --
  -- Given a list of type variables and qualifiers, substitute for each,
  -- updating the state as necessary.
  subst who state γqes0
    | M.null γqes0 = return state
    | otherwise      = do
    traceN 4 (who, γqes0, state)
    let sanitize _    []  []
          = fail $ "BUG! (subst)" ++ who ++
                   " attempt impossible substitution: " ++ show γqes0
        sanitize _    acc []
          = unsafeSubst state (M.fromDistinctAscList (reverse acc))
        sanitize seen acc ((γ, QE q γs):rest)
          | S.member γ (S.union seen γs)
          = sanitize seen acc rest
          | otherwise
          = sanitize (seen `S.union` γs) ((γ, QE q γs):acc) rest
    sanitize S.empty [] (M.toAscList γqes0)
  --
  -- This does the main work of substitution, and it has a funny
  -- precondition (which is enforced by 'subst', above), namely:
  -- the type variables will be substituted in increasing order, so the
  -- image of later variables must not contain earlier variables.
  --
  -- This is okay:     { 1 ↦ 2 3, 2 ↦ 4 }
  -- This is not okay: { 1 ↦ 3 4, 2 ↦ 1 }
  unsafeSubst state γqes = do
    sequence [ do
                 let τ = toQualifierType qe
                 writeTV γ τ
                 updatePinnedTVs γ τ
             | (γ, qe) ← M.toList γqes ]
    let γset          = M.keysSet γqes
        unchanged set = S.null (γset `S.intersection` set)
        (βlst, βlst') = List.partition (unchanged . snd) (sq_βlst state)
        (vmap, vmap') = M.partitionWithKey
                          (curry (unchanged . M.keysSet . ftvPure))
                          (sq_vmap state)
    ineqs ← stdize $
      [ (toQualifierType ql, toQualifierType (QE U βs))
      | (ql, βs) ← βlst' ]
        ++
      [ (fvTy γ, toQualifierType qe)
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
      []  → fail "Type error: qualifier constraints unsatisfiable"
      sat:_ | doIt
          → subst "sat" state =<<
              M.fromDistinctAscList <$> sequence
                [ do
                    slack ← case var of
                      QInvariant → S.singleton <$> newTV' QualKd
                      _          → return S.empty
                    -- warn $ "\nSAT: substituting " ++ show (QE q slack) ++
                    --        " for type variable " ++ show δ
                    return (δ, QE q slack)
                | δ ← S.toAscList (sq_αs state)
                , unifiable state δ
                , let (q, var) = decodeSatVar δ (sq_τftv state) sat
                , q /= U || var /= QInvariant ]
      _   → return state
  --
  toSat state = foldr (SAT.:&&:) SAT.Yes $
      [ (πa τftv q ==> πa τftv (U,βs))
      | (q, βs) ← sq_βlst state ]
    ++
      [ (πa τftv (FreeVar α) ==> πa τftv (q,αs))
      | (α, QEMeet qes) ← M.toList (sq_vmap state)
      , QE q αs         ← qes
      , unifiable state α ]
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
      getBound α = case M.lookup α (sq_vmap state) of
        Nothing           → maxBound
        Just (QEMeet qes) → bigMeet (map qeQLit qes)
  --
  -- Turn the decomposed constraint back into a list of pairs of types.
  recompose state =
      [ (fvTy γ, clean (q, βs))
      | (γ, QEMeet qem) ← M.toList (sq_vmap state)
      , γ `S.notMember` sq_αs state
      , QE q βs ← qem ]
    ++
      [ (toQualifierType q, clean (U, βs))
      | (q, βs) ← sq_βlst state ]
    where
    clean (q, βs) = toQualifierType (q, βs S.\\ sq_αs state)
  --
  makeQE q = do
    QExp ql γs ← qualifier (toQualifierType q)
    let (γs', qls) = partitionJust tvQual (fromVar <$> γs)
    return (QE (ql ⊔ bigJoin qls) (S.fromList γs'))
  --
  fromVar (FreeVar α) = α
  fromVar _           = error "BUG! solveQualifiers got bound tyvar"
  --
  unifiable _ α = tvKindIs QualKd α

-- | Update a type variable variance map as a result of substituting a
--   qualifier expression for a type variable.
substQE ∷ Ord tv ⇒ tv → QE tv → VarMap tv → VarMap tv
substQE β (QE _ βs) vmap = case takeMap β vmap of
  (Just v, vmap') → M.unionWith (⊔) vmap' (setToMap v βs)
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

class SATable a v where
  πa ∷ VarMap v → a → SAT.Boolean

instance SATable QLit v where
  πa _ ql | A ⊑ ql    = SAT.Yes
          | otherwise = SAT.No

instance Tv v ⇒ SATable (Var v) v where
  πa vm (FreeVar β) = encodeSatVar β vm
  πa _  _           = SAT.No

instance (Tv v, SATable (Var v) v) ⇒ SATable (QLit, S.Set v) v where
  πa vm (q, vs) = S.fold ((SAT.:||:) . πa vm . FreeVar) (πa vm q) vs

-- | Given a type variable and a SAT solution, return a bound
--   for that type variable as implied by the solution.
decodeSatVar ∷ Tv tv ⇒ tv → VarMap tv → SAT.SatSolver → (QLit, Variance)
decodeSatVar β vm solver = (q, var) where
  (maximize, var) = maximizeVariance β vm
  q   = case (maximize, mba) of
    -- For minimizing variables, each component tells us whether that
    -- component may be omitted from the substitution, so we choose the
    -- smallest qualifier literal that includes the required components.
    (False, Just False) → A
    (False, _         ) → U
    -- For maximizing variables, each component tells us whether that
    -- component may be included in the substitution, so we choose the
    -- largest qualifier literal that omits the forbidden components.
    (True , Just False) → U
    (True , _         ) → A
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

instance Ppr SAT.Boolean where ppr = Ppr.text . show
instance Ppr SAT.SatSolver where ppr = Ppr.text . show

-}

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

