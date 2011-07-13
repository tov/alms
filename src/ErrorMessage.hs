{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      QuasiQuotes
      #-}
module ErrorMessage (
  AlmsException(..), Phase(..),
  MonadAlmsError(..), finallyAlms, mapAlmsException,
  throw, almsBug, (!::), appendToMessage,
  wordsMsg, quoteMsg, pprMsg, showMsg, emptyMsg,
  module Message.Quasi,
) where

import Data.Loc
import Syntax.PprClass
import Message.AST
import Message.Render ()
import Message.Quasi

import Data.Typeable (Typeable)
import Control.Exception (Exception, throwIO, throw, catch)

import Control.Monad.Trans.Identity as Identity
import Control.Monad.Trans.Maybe as Maybe
import Control.Monad.Trans.List as List
import Control.Monad.Error as Error
import Control.Monad.Trans.Reader as Reader
import Control.Monad.Trans.RWS.Strict as StrictRWS
import Control.Monad.Trans.RWS.Lazy   as LazyRWS
import Control.Monad.Trans.State.Strict as StrictState
import Control.Monad.Trans.State.Lazy   as LazyState
import Control.Monad.Trans.Writer.Strict as StrictWriter
import Control.Monad.Trans.Writer.Lazy   as LazyWriter

--
-- Representation of Alms errors
--

-- | Alms internal exceptions
data AlmsException
  = AlmsException {
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

almsBug :: Phase -> Loc -> String -> String -> AlmsException
almsBug phase loc culprit0 msg0 =
  let culprit = if null culprit0
                  then "unknown"
                  else culprit0 in
  AlmsException (OtherError "BUG! in Alms implementation")
                bogus
                [msg|
                  This shouldn’t happen, so it probably
                  indicates a bug in the Alms implementation.
                  <p>
                  Details:
                  <dl>
                    <dt>who:  <dd>$words:culprit
                    <dt>what: <dd>$words:msg0
                    <dt>where:<dd>$show:loc
                    <dt>when: <dd>$show:phase
                  </dl>
                  <p>
                  Please report to <exact><tov@ccs.neu.edu></exact>.
                |]

(!::) :: Ppr a => String -> a -> Message d
msg0 !:: thing = [msg| $words:msg0 <q>$thing</q> |]
infix 1 !::

-- | Append a message to the end of the message of an 'AlmsException'
appendToMessage :: AlmsException -> Message d -> AlmsException
appendToMessage exn message =
  exn { exnMessage = [msg| $1 <br> $2 |] (exnMessage exn) message }

---
--- The MonadAlmsError class for carrying alms errors
---

class Monad m => MonadAlmsError m where
  throwAlms :: AlmsException -> m a
  catchAlms :: m a -> (AlmsException -> m a) -> m a
  unTryAlms :: m (Either AlmsException a) -> m a
  unTryAlms  = (>>= either throwAlms return)

infixl 1 `catchAlms`

finallyAlms :: MonadAlmsError m =>
               m a -> m () -> m a
finallyAlms action cleanup = do
  result <- action `catchAlms` (>>) cleanup . throwAlms
  cleanup
  return result

infixl 1 `finallyAlms`

mapAlmsException :: MonadAlmsError m =>
                    (AlmsException -> AlmsException) ->
                    m a -> m a
mapAlmsException f action = action `catchAlms` throwAlms . f

--
-- Instances
--

instance MonadAlmsError IO where
  throwAlms = throwIO
  catchAlms = Control.Exception.catch

instance MonadAlmsError (Either AlmsException) where
  throwAlms = Left
  catchAlms (Right a) _ = Right a
  catchAlms (Left e)  k = k e

instance Monad m => MonadAlmsError (ErrorT AlmsException m) where
  throwAlms = throwError
  catchAlms = catchError

--
-- Pass-through instances
--

instance MonadAlmsError m => MonadAlmsError (IdentityT m) where
  throwAlms = lift . throwAlms
  catchAlms = Identity.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (MaybeT m) where
  throwAlms = lift . throwAlms
  catchAlms = Maybe.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (ListT m) where
  throwAlms = lift . throwAlms
  catchAlms = List.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (ReaderT r m) where
  throwAlms = lift . throwAlms
  catchAlms = Reader.liftCatch catchAlms

instance (MonadAlmsError m, Monoid w) =>
         MonadAlmsError (StrictRWS.RWST r w s m) where
  throwAlms = lift . throwAlms
  catchAlms = StrictRWS.liftCatch catchAlms

instance (MonadAlmsError m, Monoid w) =>
         MonadAlmsError (LazyRWS.RWST r w s m) where
  throwAlms = lift . throwAlms
  catchAlms = LazyRWS.liftCatch catchAlms

instance (MonadAlmsError m, Monoid w) =>
         MonadAlmsError (StrictWriter.WriterT w m) where
  throwAlms = lift . throwAlms
  catchAlms = StrictWriter.liftCatch catchAlms

instance (MonadAlmsError m, Monoid w) =>
         MonadAlmsError (LazyWriter.WriterT w m) where
  throwAlms = lift . throwAlms
  catchAlms = LazyWriter.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (StrictState.StateT s m) where
  throwAlms = lift . throwAlms
  catchAlms = StrictState.liftCatch catchAlms

instance MonadAlmsError m => MonadAlmsError (LazyState.StateT s m) where
  throwAlms = lift . throwAlms
  catchAlms = LazyState.liftCatch catchAlms

---
--- 'AlmsException' Instances
---

instance Ppr AlmsException where
  ppr (AlmsException phase loc msg0) =
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

instance Show AlmsException where showsPrec = showFromPpr

instance Exception AlmsException

instance Error AlmsException where
  strMsg = AlmsException (OtherError "Error") bogus . Words

