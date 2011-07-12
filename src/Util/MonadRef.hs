{-#
  LANGUAGE
    FlexibleInstances,
    FunctionalDependencies,
    MultiParamTypeClasses,
    UndecidableInstances,
    UnicodeSyntax
  #-}
module Util.MonadRef (
  MonadRef(..),
  UnsafeReadRef(..),
) where

import Control.Monad.ST
import Control.Monad.STM

import Data.IORef
import Data.STRef
import Control.Concurrent.STM.TVar

import Control.Monad.Cont
import Control.Monad.Error
import Control.Monad.List
import Control.Monad.RWS.Strict    as Strict
import Control.Monad.RWS.Lazy      as Lazy
import Control.Monad.Reader
import Control.Monad.State.Strict  as Strict
import Control.Monad.State.Lazy    as Lazy
import Control.Monad.Writer.Strict as Strict
import Control.Monad.Writer.Lazy   as Lazy

import System.IO.Unsafe

import Util.Eq1

-- | A class for monads with mutable references. Provides generic
--   operations for creating, reading, writing, and modifying
--   references.
class (UnsafeReadRef p, Monad m, Eq1 p) ⇒ MonadRef p m | m → p where
  newRef    ∷ a → m (p a)
  readRef   ∷ p a → m a
  writeRef  ∷ p a → a → m ()
  modifyRef ∷ (a → a) → p a → m ()
  modifyRef f r = do
    a ← readRef r
    writeRef r (f a)

class UnsafeReadRef p where
  unsafeReadRef ∷ p a → a

---
--- Other MonadRef instances
---

instance MonadRef IORef IO where
  newRef   = newIORef
  readRef  = readIORef
  writeRef = writeIORef

instance UnsafeReadRef IORef where
  unsafeReadRef = unsafePerformIO . readRef

instance MonadRef (STRef s) (ST s) where
  newRef   = newSTRef
  readRef  = readSTRef
  writeRef = writeSTRef

instance UnsafeReadRef (STRef s) where
  unsafeReadRef = unsafePerformIO . unsafeSTToIO . readRef

instance MonadRef TVar STM where
  newRef   = newTVar
  readRef  = readTVar
  writeRef = writeTVar

instance UnsafeReadRef TVar where
  unsafeReadRef = unsafePerformIO . atomically . readRef

instance MonadRef p m ⇒ MonadRef p (ContT r m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Show e, Error e, MonadRef p m) ⇒ MonadRef p (ErrorT e m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance MonadRef p m ⇒ MonadRef p (ListT m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Monoid w, MonadRef p m) ⇒
         MonadRef p (Strict.RWST r w s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Monoid w, MonadRef p m) ⇒
         MonadRef p (Lazy.RWST r w s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (MonadRef p m) ⇒ MonadRef p (ReaderT r m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (MonadRef p m) ⇒ MonadRef p (Strict.StateT s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (MonadRef p m) ⇒ MonadRef p (Lazy.StateT s m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Monoid w, MonadRef p m) ⇒ MonadRef p (Strict.WriterT w m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

instance (Monoid w, MonadRef p m) ⇒ MonadRef p (Lazy.WriterT w m) where
  newRef a     = lift $ newRef a
  readRef r    = lift $ readRef r
  writeRef r a = lift $ writeRef r a

