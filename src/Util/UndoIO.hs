-- | An extension of the IO monad with an undo facility
module Util.UndoIO (
  -- * The 'UndoIO' monad
  UndoIO(..),
  -- ** Running
  runUndoIO, runUndoIO',
  -- ** Operation
  addUndo
) where

import Prelude hiding (catch)
import Util.MonadRef
import Control.Applicative
import Control.Exception
import Control.Monad.Error
import Control.Monad
import Control.Monad.Trans
import Data.IORef

import Debug.Trace

-- | A layer on top of the IO monad with an undo facility.
newtype UndoIO a
  = UndoIO {
      unUndoIO ∷ IORef [IO ()] → IO a
    }
  deriving Functor

instance Applicative UndoIO where
  pure    = return
  (<*>)   = ap

instance Monad UndoIO where
  return  = UndoIO . const . return
  m >>= k = UndoIO $ \undo → do
    a ← unUndoIO m undo
    unUndoIO (k a) undo

instance MonadIO UndoIO where
  liftIO = UndoIO . const

-- | Run an 'UndoIO' computation, running the undo list actions
--   if it raises an exception.
runUndoIO ∷ UndoIO a → IO a
runUndoIO action = do
  undo ← newRef []
  unUndoIO action undo `catch` \e → do
    sequence_ =<< readRef undo
    throwIO (e ∷ SomeException)

-- | Run an 'UndoIO' computation, without checking for an escaping
--   exception.
runUndoIO' ∷ UndoIO a → IO a
runUndoIO' action = unUndoIO action =<< newRef []

---
--- OPERATIONS
---

-- | Add an action to the front of the undo list
addUndo ∷ IO () → UndoIO ()
addUndo action = UndoIO (modifyRef (action :))

instance MonadRef IORef UndoIO where
  newRef        = UndoIO . const . newRef
  readRef       = UndoIO . const . readRef
  writeRef r a  = modifyRef (const a) r
  modifyRef f r = UndoIO $ \undo → do
    old ← readRef r
    writeRef r (f old)
    modifyRef (writeRef r old :) undo

instance MonadError SomeException UndoIO where
  throwError = liftIO . throwIO
  catchError action handler = UndoIO $ \undo → do
    undo' ← newRef []
    unUndoIO action undo' `catch` \exn → do
      sequence_ =<< readRef undo'
      unUndoIO (handler exn) undo
