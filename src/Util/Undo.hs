{-# LANGUAGE ConstraintKinds, TypeFamilies #-}
-- | An extension of the IO monad with an undo facility
module Util.Undo (
  -- * The 'UndoT' monad transformer and 'UndoIO' monad
  UndoT(..), UndoIO,
  -- ** Running
  runUndoT, runUndoT',
  runUndoIO, runUndoIO',
  -- ** Operation
  addUndo
) where

import Prelude
import Util.MonadRef
import Control.Applicative
import Control.Monad.Error
import Data.IORef

-- | A layer on top of the IO monad with an undo facility.
type UndoIO a = UndoT IORef IO a

newtype UndoT r m a
  = UndoT {
      unUndoT ∷ r [m ()] → m a
    }

instance Applicative m => Applicative (UndoT r m) where
  pure                = UndoT . const . pure
  UndoT f <*> UndoT a = UndoT (liftA2 (<*>) f a)

instance Functor m => Functor (UndoT r m) where
  fmap f = UndoT . (fmap f .) . unUndoT

instance Monad m => Monad (UndoT r m) where
  return  = lift . return
  m >>= k = UndoT $ \undo → do
    a ← unUndoT m undo
    unUndoT (k a) undo

instance MonadTrans (UndoT r) where
  lift = UndoT . const

instance MonadIO m => MonadIO (UndoT r m) where
  liftIO = lift . liftIO

-- | Run an 'UndoT' computation, running the undo list actions
--   if it raises an exception.
runUndoT ∷ (MonadError e m, MonadRef r m) => UndoT r m a → m a
runUndoT action = do
  undo ← newRef []
  unUndoT action undo `catchError` \e → do
    sequence_ =<< readRef undo
    throwError e

-- | Run an 'UndoT' computation, without checking for an escaping
--   exception.
runUndoT' ∷ MonadRef r m => UndoT r m a → m a
runUndoT' action = unUndoT action =<< newRef []

-- | Run an 'UndoIO' computation, running the undo list actions
--   if it raises an exception.
runUndoIO ∷ UndoIO a → IO a
runUndoIO = runUndoT

-- | Run an 'UndoT' computation, without checking for an escaping
--   exception.
runUndoIO' ∷ UndoIO a → IO a
runUndoIO' = runUndoT'

---
--- OPERATIONS
---

-- | Add an action to the front of the undo list
addUndo ∷ MonadRef r m => m () → UndoT r m ()
addUndo action = UndoT (modifyRef (action :))

instance MonadRef r m => MonadRef r (UndoT r m) where
  newRef        = lift . newRef
  readRef       = lift . readRef
  writeRef r a  = modifyRef (const a) r
  modifyRef f r = UndoT $ \undo → do
    old ← readRef r
    writeRef r (f old)
    modifyRef (writeRef r old :) undo

instance (MonadError e m, MonadRef r m) => MonadError e (UndoT r m) where
  throwError = lift . throwError
  catchError action handler = UndoT $ \undo → do
    undo' ← newRef []
    unUndoT action undo' `catchError` \exn → do
      sequence_ =<< readRef undo'
      unUndoT (handler exn) undo

