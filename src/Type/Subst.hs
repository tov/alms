{-# LANGUAGE
      ExistentialQuantification,
      FlexibleInstances,
      FunctionalDependencies,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      RankNTypes,
      TypeSynonymInstances,
      UndecidableInstances,
      UnicodeSyntax
    #-}
-- | Representation of type variables and substitution
module Type.Subst (
  -- * Substitution monads
  MonadSubst(..),
  -- ** New type variables
  newTV', newTVTy', newTV, newTVTy,
  -- ** Reading and writing type variables
  readTV, writeTV, rewriteTV, rootTV, derefTV,
  -- ** Rank management
  Rank, lowerRank, lowerTVRank, getTVRank,
  -- ** Change tracking
  whileChanging, iterChanging, (>=>!), collectTVs_,

  -- * A 'MonadSubst' implementation
  SubstT, TV, SubstState, substState0,
  -- ** Running
  runSubstT, runEitherSubstT,
  Subst, runSubst,
  mapSubstT,

  -- * Substitution
  Substitutable(..),

  module Util.Trace,
) where

import Util
import Util.MonadRef
import Util.Trace
import Error
import Syntax.PprClass as Ppr
import Syntax.Prec (precEq)
import Rank (Rank)
import qualified AST
import qualified Rank
import Type.Internal
import Type.TyVar
import Type.Ppr ()

import Prelude ()
import Control.Monad.ST (runST)

---
--- A SUBSTITUTION MONAD INTERFACE
---

-- | A class supporting substitutable type variables
class (Functor m, Applicative m, Tv tv,
       MonadRef r m, MonadTrace m, MonadAlmsError m) ⇒
      MonadSubst tv r m | m → tv r where
  -- | Create a new type variable.
  newTV_        ∷ (Flavor, Kind, QLit, Doc) → m tv
  -- | Write a type variable. (Not for client use.)
  writeTV_      ∷ tv → Type tv → m ()
  -- | Read a type variable.
  readTV_       ∷ tv → m (Maybe (Type tv))
  -- | Get the rank of a type variable. (Not for client use.)
  getTVRank_    ∷ tv → m (Maybe Rank)
  -- | Set the rank of a type variable. (Not for client use.)
  setTVRank_    ∷ Rank → tv → m ()
  --
  -- | Get all the type variables allocated while running the
  --   action (except for any masked out by 'collectTV' already)
  collectTVs    ∷ m a → m (a, [tv])
  -- | Report a type variable as "new" to any upstream collectors
  reportTVs     ∷ [tv] → m ()
  --
  -- | Monitor an action for changes to variables
  monitorChange ∷ m a → m (a, Bool)
  -- | Indicate that a variable has changed
  setChanged    ∷ m ()

-- | Class for constructing new type variables with a variety of
--   attributes.
class NewTV a where
  newTVArg ∷ a → (Flavor, Kind, QLit, Doc) → (Flavor, Kind, QLit, Doc)
  newTV'   ∷ MonadSubst tv r m ⇒ a → m tv
  newTV' a = newTV_ (newTVArg a (Universal, KdType, maxBound, mempty))
  newTVTy' ∷ MonadSubst tv r m ⇒ a → m (Type tv)
  newTVTy' = fvTy <$$> newTV'

instance (NewTV a, NewTV b, NewTV c, NewTV d) ⇒ NewTV (a, b, c, d) where
  newTVArg (a, b, c, d) = newTVArg a . newTVArg b . newTVArg c . newTVArg d
instance (NewTV a, NewTV b, NewTV c) ⇒ NewTV (a, b, c) where
  newTVArg (a, b, c) = newTVArg a . newTVArg b . newTVArg c
instance (NewTV a, NewTV b) ⇒ NewTV (a, b) where
  newTVArg (a, b) = newTVArg a . newTVArg b
instance AST.Tag i ⇒ NewTV (AST.TyVar i)  where
  newTVArg tv = newTVArg (AST.tvqual tv, ppr (AST.tvqual tv))
instance NewTV Flavor         where newTVArg = upd1
instance NewTV Kind           where newTVArg = upd2
instance NewTV Variance       where newTVArg = upd2 . varianceToKind
instance NewTV QLit           where newTVArg = upd3
instance NewTV Doc            where newTVArg = upd4
instance NewTV String         where newTVArg = upd4 . text
instance NewTV ()             where newTVArg = const id

substBug        ∷ MonadSubst tv r m ⇒ String → String → m a
substBug        = throwAlms <$$> almsBug StaticsPhase

-- Allocate a new, empty (unifiable) type variable
newTV           ∷ MonadSubst tv r m ⇒ m tv
newTV           = newTV' ()

-- | Allocate a new type variable and wrap it in a type
newTVTy         ∷ MonadSubst tv r m ⇒ m (Type tv)
newTVTy         = fvTy <$> newTV

-- | Get the canonical representative (root) of a tree of type
--   variables, and any non-tv type stored at the root, if it
--   exists.  Performs path compression.
rootTV          ∷ MonadSubst tv r m ⇒ tv → m (tv, Maybe (Type tv))
rootTV α = do
  mτ ← readTV_ α
  case mτ of
    Just (TyVar (Free α')) → do
      (α'', mτ') ← rootTV α'
      when (α'' /= α') $ writeTV_ α (fvTy α'')
      return (α'', mτ')
    Just τ  → return (α, Just τ)
    Nothing → return (α, Nothing)

-- | Follow a type variable to the end of the chain, whatever that is.
derefTV         ∷ MonadSubst tv r m ⇒ tv → m (Type tv)
derefTV         = liftM (uncurry (fromMaybe . fvTy)) . rootTV

-- | Read a type variable
readTV          ∷ MonadSubst tv r m ⇒ tv → m (Either tv (Type tv))
readTV          = uncurry (flip maybe Right . Left) <$$> rootTV

-- | Write a type into an empty type variable.
writeTV         ∷ MonadSubst tv r m ⇒ tv → Type tv → m ()
writeTV α τ = do
  setChanged
  (α', mτα) ← rootTV α
  traceN 2 ("writeTV", α', τ)
  case mτα of
    Nothing → do
      Just rank ← getTVRank_ α'
      lowerRank rank τ
      writeTV_ α' τ
    Just _  → substBug "writeTV" "Tried to overwrite type variable."

-- | Write a type into a type variable, even if it's not empty.
rewriteTV       ∷ MonadSubst tv r m ⇒ tv → Type tv → m ()
rewriteTV α τ = do
  setChanged
  (α', mτα) ← rootTV α
  traceN 2 ("rewriteTV", (α', mτα), τ)
  writeTV_ α' τ

-- | Lower the rank of a type variable
lowerTVRank     ∷ MonadSubst tv r m ⇒ Rank → tv → m ()
lowerTVRank r tv = do
  r0 ← getTVRank tv
  when (r < r0) (setTVRank_ r tv)

-- | Find out the rank of a type variable.
getTVRank       ∷ MonadSubst tv r m ⇒ tv → m Rank
getTVRank       = fromMaybe Rank.infinity <$$> getTVRank_

-- | Lower the rank of all the type variables in a given type
lowerRank ∷ (MonadSubst tv r m, Ftv a tv) ⇒
            Rank → a → m ()
lowerRank rank τ = mapM_ (lowerTVRank rank) (ftvList τ)

-- | Collect type variables, discarding the result.
collectTVs_     ∷ MonadSubst tv r m ⇒ m a → m [tv]
collectTVs_     = snd <$$> collectTVs

-- | Iterate a computation until it stops changing
whileChanging ∷ MonadSubst tv r m ⇒ m a → m a
whileChanging m = do
  (r, b) ← monitorChange m
  if b
    then whileChanging m
    else return r

-- | Iterate a Kleisli arrow until it stops changing.
iterChanging ∷ MonadSubst tv r m ⇒ (a → m a) → a → m a
iterChanging f z = do
  (z', b) ← monitorChange (f z)
  if b
    then iterChanging f z'
    else return z'

-- | Compose two Kleisli arrows, running the second only if the first
--   had no effect.
(>=>!) ∷ MonadSubst tv r m ⇒ (a → m a) → (a → m a) → a → m a
(>=>!) m n z = do
  (z', changed) ← monitorChange (m z)
  if changed
    then return z'
    else n z

infixr 1 >=>!

---
--- A REPRESENTATION OF FREE TYPE VARIABLES
---

-- | A free type variable
data TV r
   = UnsafeReadRef r ⇒ TV {
      tvId      ∷ !Int,
      tvKind_   ∷ !Kind,
      tvDescr_  ∷ !Doc,
      tvRep     ∷ !(TVRep r)
   }

-- | The flavor-dependent representation of a free type variable
data TVRep r
  = UniFl !(r (Either Rank (Type (TV r))))
  | ExiFl !QLit !(r Rank)
  | SkoFl !QLit

instance Eq (TV r) where
  tv1 == tv2 = tvId tv1 == tvId tv2

instance Ftv (TV r) (TV r) where
  ftvTree = FTSingle

instance Ord (TV r) where
  tv1 `compare` tv2 = tvId tv1 `compare` tvId tv2

instance Ppr (TV s) where
  ppr tv = case (debug, unsafeReadTV tv) of
    (True, Just t) →
      if debugLevel > 4
        then int (tvId tv) <> char '=' <> pprPrec precEq t
        else ppr t
    _              → text (uglyTvName tv)

instance Show (TV s) where
  showsPrec = showFromPpr

instance Tv (TV r) where
  tvUniqueID    = tvId
  tvKind        = tvKind_
  tvDescr       = tvDescr_
  tvFlavor TV { tvRep = UniFl _ }       = Universal
  tvFlavor TV { tvRep = ExiFl _ _ }     = Existential
  tvFlavor TV { tvRep = SkoFl _ }       = Skolem
  tvQual   TV { tvRep = UniFl _ }       = Nothing
  tvQual   TV { tvRep = ExiFl q _ }     = Just q
  tvQual   TV { tvRep = SkoFl q }       = Just q
  unsafeReadTV TV { tvRep = UniFl r }   =
    (const Nothing ||| Just) (unsafeReadRef r)
  unsafeReadTV _                        = Nothing

---
--- A MonadSubst IMPLEMENTATION
---

-- | Monad transformer implementing 'MonadSubst'.
newtype SubstT s m a
  = SubstT {
      unSubstT ∷ RWST () ([TV s], Any) SubstState m a
    }
  deriving (Monad, MonadTrans)

-- | The threaded state.
data SubstState
  = SubstState {
      stsGensym ∷ !Int,
      stsTrace  ∷ !Int
    }

instance Monad m ⇒ Functor (SubstT s m) where
  fmap f m = m >>= return . f

instance Monad m ⇒ Applicative (SubstT s m) where
  pure  = return
  (<*>) = ap

instance Monad m ⇒ MonadTrace (SubstT s m) where
  getTraceIndent   = SubstT (gets stsTrace)
  putTraceIndent n = SubstT (modify (\sts → sts { stsTrace = n }))

instance MonadAlmsError m ⇒ MonadAlmsError (SubstT s m) where
  getLocation       = lift getLocation
  catchAlms m h     = SubstT (catchAlms (unSubstT m) (unSubstT . h))
  withLocation_ loc = SubstT . withLocation_ loc . unSubstT
  bailoutAlms_      = lift bailoutAlms_
  reportAlms_       = lift <$> reportAlms_

instance MonadAlmsError m ⇒ MonadError [AlmsError] (SubstT s m) where
  throwError     = throwAlmsList
  catchError     = catchAlms

instance MonadRef r m ⇒ MonadRef r (SubstT r m) where
  newRef    = lift <$> newRef
  readRef   = lift <$> readRef
  writeRef  = lift <$$> writeRef
  modifyRef = lift <$$> modifyRef

instance (MonadRef r m, MonadAlmsError m) ⇒
         MonadSubst (TV r) r (SubstT r m) where
  newTV_ (flavor, kind, bound, descr) = do
    when (flavor == Universal && bound /= maxBound) $
      substBug "newTV_" "Universal tyvars cannot have non-A bound"
    sts ← SubstT get
    let i = stsGensym sts
    SubstT $ put sts { stsGensym = succ i }
    traceN 2 ("new", flavor, kind, i)
    α ← TV i kind descr <$> case flavor of
      Universal   → UniFl <$> newRef (Left Rank.infinity)
      Existential → ExiFl bound <$> newRef Rank.infinity
      Skolem      → return $ SkoFl bound
    SubstT $ tell ([α], mempty)
    return α
  writeTV_ TV { tvRep = UniFl r }   t = writeRef r (Right t)
  writeTV_ TV { tvRep = ExiFl _ _ } _ = substBug "writeTV_" "got existential"
  writeTV_ TV { tvRep = SkoFl _ }   _ = substBug "writeTV_" "got skolem"
  readTV_ TV { tvRep = UniFl r } = (const Nothing ||| Just) <$> readRef r
  readTV_ _                      = return Nothing
  --
  getTVRank_ TV { tvRep = UniFl r }   = (Just ||| const Nothing ) <$> readRef r
  getTVRank_ TV { tvRep = ExiFl _ r } = Just <$> readRef r
  getTVRank_ TV { tvRep = SkoFl _ }   = return Nothing
  setTVRank_ rank TV { tvRep = UniFl r }   = writeRef r (Left rank)
  setTVRank_ rank TV { tvRep = ExiFl _ r } = writeRef r rank
  setTVRank_ _    TV { tvRep = SkoFl _ }   = return ()
  --
  collectTVs action = do
    rαs ← (SubstT . censor (upd1 []) . listens sel1 . unSubstT) action
    traceN 2 ("collectTV", snd rαs)
    return rαs
  reportTVs αs = SubstT (tell (αs, mempty))
  --
  monitorChange = SubstT . listens (getAny . sel2) . unSubstT
  setChanged    = SubstT $ tell ([], Any True)

--
-- Pass-through instances
--

instance (MonadSubst tv r m, Monoid w) ⇒ MonadSubst tv r (WriterT w m) where
  newTV_        = lift <$> newTV_
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  collectTVs    = mapWriterT (mapListen2 collectTVs)
  reportTVs     = lift <$> reportTVs
  monitorChange = mapWriterT (mapListen2 monitorChange)
  setChanged    = lift setChanged

instance MonadSubst tv r m ⇒ MonadSubst tv r (StateT s m) where
  newTV_        = lift <$> newTV_
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  collectTVs    = mapStateT (mapListen2 collectTVs)
  reportTVs     = lift <$> reportTVs
  monitorChange = mapStateT (mapListen2 monitorChange)
  setChanged    = lift setChanged

instance MonadSubst tv r m ⇒ MonadSubst tv r (ReaderT r' m) where
  newTV_        = lift <$> newTV_
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  collectTVs    = mapReaderT collectTVs
  reportTVs     = lift <$> reportTVs
  monitorChange = mapReaderT monitorChange
  setChanged    = lift setChanged

instance (MonadSubst tv r m, Monoid w) ⇒ MonadSubst tv r (RWST r' w s m) where
  newTV_        = lift <$> newTV_
  writeTV_      = lift <$$> writeTV_
  readTV_       = lift <$> readTV_
  getTVRank_    = lift <$> getTVRank_
  setTVRank_    = lift <$$> setTVRank_
  collectTVs    = mapRWST (mapListen3 collectTVs)
  reportTVs     = lift <$> reportTVs
  monitorChange = mapRWST (mapListen3 monitorChange)
  setChanged    = lift setChanged

--
-- Running
--

-- | Run in the substitution monad
runSubstT ∷ Monad m ⇒ SubstState → SubstT r m a → m (a, SubstState)
runSubstT state0 (SubstT m) = do
  (result, state, _) ← runRWST m () state0 { stsTrace = 0 }
  return (result, state)

substState0 ∷ SubstState
substState0 = SubstState 0 0

-- | Run a substitution computation, but not inheriting exception
--   handling
runEitherSubstT ∷ Monad m ⇒
                 SubstState → SubstT r (AlmsErrorT m) a →
                 m (Either [AlmsError] (a, SubstState))
runEitherSubstT = runAlmsErrorT <$$> runSubstT

-- | The type of a generic substitution computation
type Subst a  = ∀ s m. (MonadRef s m, MonadAlmsError m) ⇒ SubstT s m a

-- | Run a substitution computation in a pure context
runSubst ∷ SubstState → Subst a → Either [AlmsError] (a, SubstState)
runSubst st0 m = runST (runEitherSubstT st0 m)

-- | For lifting through 'SubstT'
mapSubstT ∷ (Functor t1, Functor t2) ⇒
            (∀s. t1 (a, s) → t2 (b, s)) →
            SubstT r t1 a → SubstT r t2 b
mapSubstT f = SubstT . mapRWST f' . unSubstT where
  f' action = fromPair <$> f (toPair <$> action)
  toPair (a, s, w)     = (a, (s, w))
  fromPair (a, (s, w)) = (a, s, w)

---
--- SUBSTITUTION
---

class Monad m ⇒ Substitutable a m where
  -- | Fully dereference all the values, deeply.
  subst         ∷ a → m a
  -- | Fully dereference a sequence of TV indirections, with path
  --   compression, at the root of a type (or each type of a
  --   collection).
  substHead     ∷ a → m a

instance Substitutable a m ⇒ Substitutable [a] m where
  subst     = mapM subst
  substHead = mapM substHead

instance Substitutable a m ⇒ Substitutable (Maybe a) m where
  subst     = mapM subst
  substHead = mapM substHead

instance (Substitutable a m, Substitutable b m) ⇒
         Substitutable (a, b) m where
  subst (a, b)     = liftM2 (,) (subst a) (subst b)
  substHead (a, b) = liftM2 (,) (substHead a) (substHead b)

instance MonadSubst tv r m ⇒ Substitutable (Type tv) m where
  subst = foldTypeM (mkQuF (return <$$$> TyQu))
                    (mkBvF (return <$$$> bvTy))
                    ((>>= either (return . fvTy) subst) . readTV)
                    (return <$$> TyApp)
                    (return <$$$> TyRow)
                    (mkMuF (return <$$> TyMu))
  substHead (TyVar (Free r)) = derefTV r
  substHead σ                = return σ

