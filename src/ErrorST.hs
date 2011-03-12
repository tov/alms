-- | A semi-transactional version of the ST monad
{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      RankNTypes #-}
module ErrorST (
  -- * The 'ST' monad with errors
  ST,
  -- ** Operations
  runST, transaction, liftST,
  catchError, throwError,
  -- * 'STRef's
  STRef,
  -- ** Operations
  newSTRef, newTransSTRef, readSTRef, writeSTRef, modifySTRef,
  unsafeIOToST
) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.State
import qualified Control.Monad.ST as Super
import Data.Data
import qualified Data.STRef as S

-- | Like the 'ST' monad, but with errors and transactions.  Each STRef
--   is declared to be transaction alor not.  Transaction STRefs lose
--   any changes made between an exception handler and an exception
--   being thrown.
newtype ST s e a = ST { unST :: Rep s e a }
  deriving (Functor, Monad, Typeable)
type Rep s e a = ErrorT e (StateT (Super.ST s ()) (Super.ST s)) a

instance Error e => Applicative (ST s e) where
  pure  = return
  (<*>) = ap

instance Error e => MonadError e (ST s e) where
  throwError = ST . throwError
  catchError body handler = ST $ do
    oldUndo <- get
    put (return ())
    do res <- unST body
       modify (>> oldUndo)
       return res
     `catchError` \e -> do
        newUndo <- get
        put oldUndo
        liftST_ newUndo
        unST (handler e)

runST :: (Error e, MonadError e m) => (forall s. ST s e a) -> m a
runST block =
  either throwError return $
    Super.runST (evalStateT (runErrorT (unST (transaction block))) (return ()))

-- | Run something directly in the underlying ST monad
liftST :: Error e => Super.ST s a -> ST s e a
liftST  = ST . liftST_

transaction :: Error e => ST s e a -> ST s e a
transaction block = block `catchError` throwError

data STRef s a
  = NonTr {
      getRef   :: !(S.STRef s a)
    }
  | Trans {
      getRef   :: !(S.STRef s a)
    }
  deriving Typeable

-- | Create a new 'STRef' whose changes survive failed transactions
newSTRef      :: Error e => a -> ST s e (STRef s a)
newSTRef       = liftM NonTr . ST . liftST_ . S.newSTRef

-- | Create a new 'STRef' whose changes are reverted by failed transactions
newTransSTRef :: Error e => a -> ST s e (STRef s a)
newTransSTRef  = liftM Trans . ST . liftST_ . S.newSTRef

readSTRef     :: Error e => STRef s a -> ST s e a
readSTRef      = ST . liftST_ . S.readSTRef . getRef

writeSTRef    :: Error e => STRef s a -> a -> ST s e ()
writeSTRef (NonTr r) a = ST . liftST_ . S.writeSTRef r $ a
writeSTRef (Trans r)  a = ST $ do
  old <- liftST_ (S.readSTRef r)
  addUndo_ (S.writeSTRef r old)
  liftST_ (S.writeSTRef r a)

modifySTRef   :: Error e => STRef s a -> (a -> a) -> ST s e ()
modifySTRef (NonTr r) f = ST . liftST_ . S.modifySTRef r $ f
modifySTRef (Trans r)  f = ST $ do
  old <- liftST_ (S.readSTRef r)
  addUndo_ (S.writeSTRef r old)
  liftST_ (S.writeSTRef r (f old))

unsafeIOToST  :: Error e => IO a -> ST s e a
unsafeIOToST   = ST . liftST_ . Super.unsafeIOToST

-- helpers

addUndo_ :: Error e => Super.ST s () -> Rep s e ()
addUndo_  = modify . (>>)

liftST_  :: Error e => Super.ST s a -> Rep s e a
liftST_   = lift . lift

{-
test :: IO ()
test = either fail id . runST $ do
  a <- newSTRef "a0"
  b <- newTransSTRef "b0"
  c <- newSTRef "c0"
  d <- newTransSTRef "d0"
  e <- newSTRef "e0"
  f <- newTransSTRef "f0"
  do
      writeSTRef a "a1"
      writeSTRef b "b1"
      writeSTRef d "d1"
      transaction $ do
        writeSTRef c "c2"
        writeSTRef d "d2"
        throwError "ERROR!"
      writeSTRef a "a3"
      writeSTRef b "b3"
    `catchError` \_ -> do
      writeSTRef e "e4"
      writeSTRef f "f4"
  ra <- readSTRef a
  rb <- readSTRef b
  rc <- readSTRef c
  rd <- readSTRef d
  re <- readSTRef e
  rf <- readSTRef f
  return $
    print [(ra, "a1"), (rb, "b0"),
           (rc, "c2"), (rd, "d0"),
           (re, "e4"), (rf, "f4")]
-}
