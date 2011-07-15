{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      QuasiQuotes,
      RankNTypes,
      TupleSections,
      UndecidableInstances,
      UnicodeSyntax
      #-}
module Error (
  AlmsError(..), Phase(..),
  almsBug, (!::), appendToMessage,
  wordsMsg, quoteMsg, pprMsg, showMsg, emptyMsg,
  throw,

  MonadAlmsError(..),
  unTryAlms, finallyAlms, mapAlmsErrors,

  AlmsErrorT(..), runAlmsErrorT,
  mapAlmsErrorT, liftCallCC, liftCatch, liftListen, liftPass,

  module Message.Quasi,
) where

import Util
import Util.MonadRef
import Util.Trace
import Data.Loc
import Syntax.PprClass
import Message.AST
import Message.Render ()
import Message.Quasi

import Prelude ()
import Data.Typeable (Typeable)
import Control.Applicative
import Control.Exception (Exception, throwIO, throw, catch)

import qualified Control.Monad.Cont as Cont
import qualified Control.Monad.Trans.Identity as Identity
import qualified Control.Monad.Trans.Maybe as Maybe
import qualified Control.Monad.Trans.List as List
import qualified Control.Monad.Error as Error
import qualified Control.Monad.Trans.Reader as Reader
import qualified Control.Monad.Trans.RWS.Strict as StrictRWS
import qualified Control.Monad.Trans.RWS.Lazy   as LazyRWS
import qualified Control.Monad.Trans.State.Strict as StrictState
import qualified Control.Monad.Trans.State.Lazy   as LazyState
import qualified Control.Monad.Trans.Writer.Strict as StrictWriter
import qualified Control.Monad.Trans.Writer.Lazy   as LazyWriter

--
-- Representation of Alms errors
--

-- | Alms internal exceptions
data AlmsError
  = AlmsError {
      exnPhase   :: Phase,    -- | When did it happen?
      exnLoc     :: Loc,      -- | Where in the source did it happen?
      exnMessage :: Message V -- | What happened?
  }
  deriving Typeable

-- | The phases in which an error might occur:
data Phase
  = ParserPhase
  | RenamerPhase
  | StaticsPhase
  | DynamicsPhase
  | OtherError String
  deriving Show

-- | Error constructors

almsBug :: Phase -> String -> String -> AlmsError
almsBug phase culprit0 msg0 =
  let culprit = if null culprit0
                  then "unknown"
                  else culprit0 in
  AlmsError (OtherError "BUG! in Alms implementation")
                bogus
                [msg|
                  This shouldn’t happen, so it probably
                  indicates a bug in the Alms implementation.
                  <p>
                  Details:
                  <dl>
                    <dt>who:  <dd>$words:culprit
                    <dt>what: <dd>$words:msg0
                    <dt>when: <dd>$show:phase
                  </dl>
                  <p>
                  Please report to <exact><tov@ccs.neu.edu></exact>.
                |]

(!::) :: Ppr a => String -> a -> Message d
msg0 !:: thing = [msg| $words:msg0 <q>$thing</q> |]
infix 1 !::

-- | Append a message to the end of the message of an 'AlmsError'
appendToMessage :: AlmsError -> Message d -> AlmsError
appendToMessage exn message =
  exn { exnMessage = [msg| $1 <br> $2 |] (exnMessage exn) message }

---
--- 'AlmsError' Instances
---

instance Ppr AlmsError where
  ppr (AlmsError phase loc msg0) =
     (text phaseString <+> locString <> colon)
     $$
     ppr (Indent msg0)
     where locString   = if isBogus loc
                           then mempty
                           else text "at" <+> text (show loc)
           phaseString = case phase of
             ParserPhase   -> "Syntax error"
             RenamerPhase  -> "Type error"
             StaticsPhase  -> "Type error"
             DynamicsPhase -> "Run-time error"
             OtherError s  -> s

instance Show AlmsError where showsPrec = showFromPpr

instance Exception AlmsError

instance Error AlmsError where
  strMsg = AlmsError (OtherError "Error") bogus . Words

---
--- The MonadAlmsError class for carrying alms errors
---

-- | A class for managing multiple errors with messages and source
--   locations.  Minimal complete definition: @getLocation@,
--   @withLocation_@, @bailoutAlms_@, @reportAlms_@, and @catchAlms@.
class Monad m => MonadAlmsError m where
  -- | Find out the current source location.
  getLocation   :: m Loc
  -- | Run a computation in the context of the given source location.
  withLocation  :: Locatable loc ⇒ loc -> m a -> m a
  -- | Add an error to the collection of errors, but keep running.
  reportAlms    :: AlmsError -> m ()
  -- | Report an error and give up running.
  throwAlms     :: AlmsError -> m a
  -- | Report some errors and give up running.
  throwAlmsList :: [AlmsError] -> m a
  -- | If any errors have occurred, collect them and give them to
  --   a handler.  The list should be non-empty.
  catchAlms     :: m a -> ([AlmsError] -> m a) -> m a
  --
  -- Low-level methods (not intended for client use)
  --
  withLocation_ :: Loc -> m a -> m a
  bailoutAlms_  :: m a
  reportAlms_   :: AlmsError -> m ()
  --
  -- Default implementations
  --
  withLocation locatable =
    let loc = getLoc locatable
     in if isBogus loc
          then id
          else withLocation_ loc
  reportAlms e      = do
    if isBogus (exnLoc e)
      then do
        loc <- getLocation
        reportAlms_ e { exnLoc = loc }
      else reportAlms_ e
  throwAlms e       = reportAlms e >> bailoutAlms_
  throwAlmsList es = mapM reportAlms es >> bailoutAlms_

unTryAlms :: MonadAlmsError m =>
             m (Either [AlmsError] a) -> m a
unTryAlms  = (either throwAlmsList return =<<)

infixl 1 `catchAlms`

finallyAlms :: MonadAlmsError m =>
               m a -> m () -> m a
finallyAlms action cleanup = do
  result <- action `catchAlms` (>>) cleanup . throwAlmsList
  cleanup
  return result

infixl 1 `finallyAlms`

mapAlmsErrors :: MonadAlmsError m =>
                 (AlmsError -> AlmsError) ->
                 m a -> m a
mapAlmsErrors f action = action `catchAlms` throwAlmsList . map f

--
-- Instances
--

-- | This doesn't work very well
instance MonadAlmsError IO where
  getLocation     = return bogus
  withLocation_ _ = id
  bailoutAlms_    = fail ""
  reportAlms_     = throwIO
  catchAlms action handler = Control.Exception.catch action handler'
    where handler' e = handler [e]

--
-- A monad transformer
--

newtype AlmsErrorT m a
  = AlmsErrorT {
      unAlmsErrorT :: Maybe.MaybeT (StrictRWS.RWST Loc [AlmsError] () m) a
    }

instance Monad m => Functor (AlmsErrorT m) where
  fmap  = liftM

instance Monad m => Applicative (AlmsErrorT m) where
  pure  = return
  (<*>) = ap

instance Monad m => Monad (AlmsErrorT m) where
  return  = AlmsErrorT . return
  m >>= k = AlmsErrorT (unAlmsErrorT m >>= (unAlmsErrorT . k))
  fail s  = throwAlms (strMsg s)

instance MonadTrans AlmsErrorT where
  lift = AlmsErrorT . lift . lift

instance Monad m => MonadAlmsError (AlmsErrorT m) where
  getLocation       = AlmsErrorT (lift ask)
  withLocation_ loc =
    AlmsErrorT . Maybe.mapMaybeT (local (const loc)) . unAlmsErrorT
  bailoutAlms_      = AlmsErrorT (Maybe.MaybeT (return Nothing))
  reportAlms_ e     = AlmsErrorT (lift (tell [e]))
  catchAlms action handler
                    = either handler return =<< lift (runAlmsErrorT action)

runAlmsErrorT :: Monad m =>
                 AlmsErrorT m a -> m (Either [AlmsError] a)
runAlmsErrorT (AlmsErrorT action) = do
  (mresult, es) <- StrictRWS.evalRWST (Maybe.runMaybeT action) bogus ()
  case (mresult, es) of
    (Just a, [])  -> return (Right a)
    (_,      [])  -> return $
      Left [almsBug (OtherError "Unknown")
                    "AlmsErrorT" "got empty error list"]
    (_,      _)   -> return (Left es)

-- | Map a higher order operation through the 'AlmsErrorT' monad
mapAlmsErrorT ∷ (m (Maybe a, (), [AlmsError]) →
                 n (Maybe b, (), [AlmsError])) →
                AlmsErrorT m a → AlmsErrorT n b
mapAlmsErrorT f =
  AlmsErrorT . Maybe.mapMaybeT (StrictRWS.mapRWST f) . unAlmsErrorT

-- | Lift a @callCC@ operation through the 'AlmsErrorT' monad
liftCallCC ∷
  ((((Maybe a, (), [AlmsError]) → m (Maybe b, (), [AlmsError])) →
    m (Maybe a, (), [AlmsError])) → m (Maybe a, (), [AlmsError])) →
  ((a → AlmsErrorT m b) → AlmsErrorT m a) →
  AlmsErrorT m a
liftCallCC callCC0 kont =
  AlmsErrorT $
    Maybe.liftCallCC (StrictRWS.liftCallCC callCC0)
                     (unAlmsErrorT . kont . (AlmsErrorT .))

-- | Lift a @catch@ operation through the 'AlmsErrorT' monad
liftCatch ∷ (∀ s. m s → (e → m s) → m s) →
            AlmsErrorT m a → (e → AlmsErrorT m a) →
            AlmsErrorT m a
liftCatch catch0 action handle =
  AlmsErrorT $
    Maybe.liftCatch (StrictRWS.liftCatch catch0)
                    (unAlmsErrorT action)
                    (unAlmsErrorT . handle)

-- | Lift a @listen@ operation through the 'AlmsErrorT' monad
liftListen ∷ Monad m ⇒
             (∀ s. m s → m (s, w)) →
             AlmsErrorT m a → AlmsErrorT m (a, w)
liftListen listen' = mapAlmsErrorT $ \action → do
  ((mresult, st, es), w) ← listen' action
  return $! case mresult of
    Nothing → (Nothing, st, es)
    Just v  → (Just (v, w), st, es)

-- | Lift a @pass@ operation through the 'AlmsErrorT' monad
liftPass ∷ Monad m ⇒
           (∀ s. m (s, w → w) → m s) →
           AlmsErrorT m (a, w → w) → AlmsErrorT m a
liftPass pass' = mapAlmsErrorT $ \action → pass' $ do
  (mresult, st, es) ← action
  return $! case mresult of
    Nothing     → ((Nothing, st, es), id)
    Just (v, f) → ((Just v, st, es), f)

--
-- AlmsErrorT Pass-through instances
--

instance MonadReader r m ⇒ MonadReader r (AlmsErrorT m) where
  ask   = lift ask
  local = mapAlmsErrorT . local

instance MonadState s m ⇒ MonadState s (AlmsErrorT m) where
  get   = lift get
  put   = lift . put

instance MonadWriter w m ⇒ MonadWriter w (AlmsErrorT m) where
  tell   = lift . tell
  listen = liftListen listen
  pass   = liftPass pass

instance MonadError e m ⇒ MonadError e (AlmsErrorT m) where
  throwError = lift . throwError
  catchError = liftCatch catchError

instance Cont.MonadCont m ⇒ Cont.MonadCont (AlmsErrorT m) where
  callCC = liftCallCC Cont.callCC

instance MonadRef r m ⇒ MonadRef r (AlmsErrorT m) where
  newRef        = lift <$> newRef
  readRef       = lift <$> readRef
  writeRef      = lift <$$> writeRef

instance MonadTrace m ⇒ MonadTrace (AlmsErrorT m) where
  getTraceIndent = lift getTraceIndent
  putTraceIndent = lift <$> putTraceIndent
  putTraceString = lift <$> putTraceString

--
-- MonadAlmsError Pass-through instances
--

instance MonadAlmsError m => MonadAlmsError (Identity.IdentityT m) where
  getLocation    = lift getLocation
  withLocation_  = Identity.mapIdentityT . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = Identity.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (Maybe.MaybeT m) where
  getLocation    = lift getLocation
  withLocation_  = Maybe.mapMaybeT . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = Maybe.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (ListT m) where
  getLocation    = lift getLocation
  withLocation_  = mapListT . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = List.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (ReaderT r m) where
  getLocation    = lift getLocation
  withLocation_  = mapReaderT . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = Reader.liftCatch catchAlms

instance (MonadAlmsError m, Monoid w) =>
         MonadAlmsError (StrictRWS.RWST r w s m) where
  getLocation    = lift getLocation
  withLocation_  = StrictRWS.mapRWST . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = StrictRWS.liftCatch catchAlms

instance (MonadAlmsError m, Monoid w) =>
         MonadAlmsError (LazyRWS.RWST r w s m) where
  getLocation    = lift getLocation
  withLocation_  = LazyRWS.mapRWST . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = LazyRWS.liftCatch catchAlms

instance (MonadAlmsError m, Monoid w) =>
         MonadAlmsError (StrictWriter.WriterT w m) where
  getLocation    = lift getLocation
  withLocation_  = StrictWriter.mapWriterT . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = StrictWriter.liftCatch catchAlms

instance (MonadAlmsError m, Monoid w) =>
         MonadAlmsError (LazyWriter.WriterT w m) where
  getLocation    = lift getLocation
  withLocation_  = LazyWriter.mapWriterT . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = LazyWriter.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (StrictState.StateT s m) where
  getLocation    = lift getLocation
  withLocation_  = StrictState.mapStateT . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = StrictState.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (LazyState.StateT s m) where
  getLocation    = lift getLocation
  withLocation_  = LazyState.mapStateT . withLocation_
  bailoutAlms_   = lift bailoutAlms_
  reportAlms_    = lift . reportAlms_
  catchAlms      = LazyState.liftCatch catchAlms

