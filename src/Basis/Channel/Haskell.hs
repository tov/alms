-----------------------------------------------------------------------------
-- |
-- Module      :  Basis.Channel.Haskell
-- Copyright   :  (c) 2009 Jesse A. Tov
-- License     :  BSD (see the file LICENSE)
-- 
-- Maintainer  :  tov@ccs.neu.edu
-- Stability   :  experimental
-- Portability :  GHC 6-7
--
-- This module provides synchronous channels.  Unlike the channels in
-- 'Control.Concurrent.Chan', which are unbounded queues on which
-- writers never block, these channels allow each writer to block until
-- it synchronizes with the particular reader that receives its message.
--
-- We actually provide three classes of channel operations:
--
--   [Synchronous, blocking] These operations block until they
--     synchronize their communication with another thread.
--
--   [Synchronous, non-blocking] These operations complete immediately
--     if another thread is ready to synchronize, and otherwise return
--     a failure code immediate.
--
--   [Asynchronous] These operations complete immediately and always
--     succeed, though the value they send may not be received until
--     another thread tries to receive it.
--
-----------------------------------------------------------------------------
module Basis.Channel.Haskell (
  -- * The channel datatype
  Chan,               -- abstract: * -> *
  -- ** Construction and observation
    newChan,            -- IO (Chan a)
    isEmptyChan,        -- Chan a -> IO Bool

  -- * Synchronous, blocking operations
  -- | The synchronous, blocking channel operations are designed
  --   to complete only when a writing thread synchronizes with a
  --   reading thread.
  --
  --   They are exception safe, in the sense that if
  --   an asynchronous exception is delivered to a blocked thread,
  --   that thread is removed from the pool and cannot synchronize
  --   with another.  In particular, we can write code like this:
  --
  --   @
  --   'Control.Exception.mask_' $ do
  --     msg <- 'readChan' c
  --     'writeIORef' r msg
  --   @
  --
  --   In this case, the call to 'readChan' may be interrupted, but
  --   if the message is delivered, the 'writeIORef' will happen.  There
  --   is no case where the writing thread synchronizes and unblocks
  --   and the message is dropped on the floor.  This make it possible
  --   to safely implement features such as timeouts on blocking
  --   operations.

  -- ** Basic operations
    writeChan,          -- Chan a -> a -> IO ()
    readChan,           -- Chan a -> IO a
  -- ** Questionable operations
    unGetChan,          -- Chan a -> a -> IO ()
    swapChan,           -- Chan a -> a -> IO a
  -- ** List operations
    getChanContents,    -- Chan a -> IO [a]
    getChanN,           -- Chan a -> Integer -> IO [a]
    writeList2Chan,     -- Chan a -> [a] -> IO ()

  -- * Synchronous, non-blocking operations
  -- | These operations are similar to the blocking operations in that
  --   they only succeed by synchronizing with another thread, but
  --   they return a failure code rather than block if no other thread
  --   is ready or if they cannot acquire a lock on the channel.
  --
  --   Generally, a non-blocking operation from this section
  --   cannot synchronize with another non-blocking operation.  The
  --   other operation that pairs up with one of these operations will
  --   always be blocking or asynchronous.
  --
  --   These operations are designed to operate in constant time
  --   (or linear time for the list operations).
  --   In particular, it may be possible to attempt to synchronize with
  --   a waiting thread that gives up before the operation is complete.
  --   Rather than look for another opportunity, which could lead to
  --   an arbitrary number of attempts, the operation fails with
  --   'TryAgain'.

  -- ** The non-blocking result datatype
  TryResult(..),      -- concrete: * -> *
    maybeTry,           -- IO (TryResult a) -> IO (Maybe a)

  -- ** Basic operations
    tryWriteChan,       -- Chan a -> a -> IO (TryResult ()
    tryReadChan,        -- Chan a -> IO (TryResult a)
    tryPeekChan,        -- Chan a -> IO (TryResult a)
  -- ** List operations
    tryGetChanContents, -- Chan a -> IO (TryResult [a])
    tryGetChanN,        -- Chan a -> Integer -> IO (TryResult [a])
    tryWriteList2Chan,  -- Chan a -> Integer -> IO (TryResult (), [a])

  -- * Asynchronous operations
  -- | The asynchronous operations always succeed immediately.
  --   They should be semantically equivalent to forking another thread
  --   and performing the equivalent blocking operation (though they do
  --   not actually require a separate thread).

    asyncWriteChan,     -- Chan a -> a -> IO ()
    asyncUnGetChan,     -- Chan a -> a -> IO ()
    tryAsyncSwapChan,   -- Chan a -> a -> IO a
    asyncWriteList2Chan -- Chan a -> [a] -> IO ()
) where

import Control.Concurrent.MVar hiding ( modifyMVar )
import Control.Monad
import Data.IORef
import System.IO.Unsafe ( unsafeInterleaveIO )

import Control.Exception ( finally, onException )
import Compat ( mask )

---
--- Amortized O(1) queues
---

data Q a = Q { readEnd :: ![a], writeEnd :: ![a] }

empty :: Q a
empty  = Q [] []

(|>) :: Q a -> a -> Q a
(|>) q a = q { writeEnd = a : writeEnd q }

(<|) :: a -> Q a -> Q a
(<|) a q = q { readEnd = a : readEnd q }

(|>>>) :: Q a -> [a] -> Q a
(|>>>) q as = Q { readEnd  = concat [ readEnd q,
                                      reverse (writeEnd q),
                                      as ],
                  writeEnd = [] }

data QView a b = !a :< !(Q a)
               | NoQ !b

dequeue :: b -> Q a -> QView a b
dequeue b (Q []     []) = NoQ b
dequeue _ (Q (r:rs) ws) = r :< Q rs ws
dequeue b (Q []     ws) = dequeue b (Q (reverse ws) [])

---
--- Chan representation
---

-- Both readers and writers include IORef (Maybe ...) in their
-- representations.  This allows \"revoking\" an operation in case the
-- blocked thread is interrupted.
--
-- A reader contains an MVar in which to write a message to it, whereas
-- a writer contains the value it has sent and an MVar on which to
-- confirm receipt of the message.  A channel at any point in time is
-- represented as either a queue of waiting writers or a queue of
-- waiting readers.
type Reader a  = (IORef (Maybe (MVar a)))
type Writer a  = (IORef (Maybe a), MVar ())
data Rep a     = RQ !(Q (Reader a))
               | WQ !(Q (Writer a))

-- | The abstract channel type for sending values of type @a@.
newtype Chan a = Chan (MVar (Rep a))
  deriving Eq

-- | The synchronous, non-blocking operations may succeed immediately,
--   or they may give up for a variety of reasons:
data TryResult a =
    -- | The operation succeeded.
    Success { getSuccess :: a }
    -- | No other thread is currently ready to synchronize for the
    --   requested operation.
  | NotReady
    -- | An attempt was made to synchronize with another thread, but
    --   the other thread bailed out before it could complete.  Another
    --   thread may be available, so it may be worth trying again
    --   immediately.
  | TryAgain
    -- | Another thread is currently operating on the channel.  It may
    --   be worth trying again very soon.
  | WouldBlock
  deriving (Eq, Show)

getReaders :: Rep a -> QView (Reader a) (Q (Writer a))
getReaders (RQ q) = dequeue empty q
getReaders (WQ q) = dequeue q empty

getWriters :: Rep a -> QView (Writer a) (Q (Reader a))
getWriters (RQ q) = dequeue q empty
getWriters (WQ q) = dequeue empty q

clear :: IO a -> IORef (Maybe b) -> IO a
clear io r = mask $ \_ -> io `finally` writeIORef r Nothing

-- | Make a new channel.
newChan :: IO (Chan a)
newChan = fmap Chan (newMVar (RQ empty))

genericWriteChan :: (Q (Writer a) -> Writer a -> Q (Writer a)) ->
                    Bool ->
                    Chan a -> a -> IO ()
genericWriteChan enq wait (Chan m) a = join $ modifyMVar m modify
  where
    modify e = case getReaders e of
      r :< readers -> do
        maybereader <- readIORef r
        case maybereader of
          Just reader -> do
            putMVar reader a
            return (RQ readers, return ())
          Nothing     ->
            modify e
      NoQ writers -> do
        r       <- newIORef (Just a)
        confirm <- newEmptyMVar
        return (WQ (writers `enq` (r, confirm)),
                if wait
                  then takeMVar confirm `clear` r
                  else return ())

-- |
-- Write a value to a channel, possibly blocking until synchronizing
-- with a reader.
writeChan :: Chan a -> a -> IO ()
writeChan = genericWriteChan (|>) True

-- |
-- Write to the \"read end\" of a channel.  If several writers are
-- waiting, this jumps ahead of them to the front of the line.  Blocks
-- until matched up with a reader.
unGetChan :: Chan a -> a -> IO ()
unGetChan  = genericWriteChan (flip (<|)) True

-- |
-- Write a value to a channel, returning immediately rather than
-- waiting for the reader to arrive.
asyncWriteChan :: Chan a -> a -> IO ()
asyncWriteChan = genericWriteChan (|>) False

-- |
-- Write a value to the \"read end\" of a channel, succeeding immediately
-- rather than waiting for a reader.
asyncUnGetChan :: Chan a -> a -> IO ()
asyncUnGetChan  = genericWriteChan (flip (<|)) False

-- |
-- Attempts to write a value to a channel, succeeding immediately
-- if a reader is already available to synchronize.  Will fail
-- if the reader is interrupted before the operation completes, if there
-- is no reader available, or if another thread is currently starting
-- an operation on the channel.
tryWriteChan :: Chan a -> a -> IO (TryResult ())
tryWriteChan (Chan m) a = tryModifyMVar m modify
  where
    modify e = case getReaders e of
      r :< readers -> do
        maybereader <- readIORef r
        case maybereader of
          Just reader -> do
            putMVar reader a
            return (RQ readers, Success ())
          Nothing ->
            return (e, TryAgain)
      NoQ _ ->
        return (e, NotReady)

-- |
-- Reads a value from a channel, potentially blocking until a writer
-- is ready to synchronize.
readChan :: Chan a -> IO a
readChan (Chan m) = join $ modifyMVar m modify
  where
    modify e = case getWriters e of
      NoQ readers -> do
        message <- newEmptyMVar
        r       <- newIORef (Just message)
        return (RQ (readers |> r),
                takeMVar message `clear` r)
      (r, confirm) :< writers -> do
        maybea <- readIORef r
        case maybea of
          Just a  -> do
            putMVar confirm ()
            return (WQ writers, return a)
          Nothing ->
            modify (WQ writers)

-- |
-- Attempts to read a value from a channel, succeeding immediately
-- if a writer is already available to synchronize.
tryReadChan :: Chan a -> IO (TryResult a)
tryReadChan (Chan m) = tryModifyMVar m modify
  where
    modify e = case getWriters e of
      NoQ _ ->
        return (e, NotReady)
      (r, confirm) :< writers -> do
        maybea <- readIORef r
        case maybea of
          Just a  -> do
            putMVar confirm ()
            return (WQ writers, Success a)
          Nothing -> do
            return (WQ writers, TryAgain)

-- |
-- Attempts to read a value from a channel, but does not allow a writer
-- to synchronize, and does not remove the observed value from the
-- channel.  Fails if no writer is currently available, if the first
-- writer has bailed, or if it cannot immediately get a lock on the
-- channel.
tryPeekChan :: Chan a -> IO (TryResult a)
tryPeekChan (Chan m) = tryModifyMVar m modify
  where
    modify e =
      case getWriters e of
        NoQ _              -> return (e, NotReady)
        (r, _) :< writers -> do
          maybea <- readIORef r
          case maybea of
            Just a  -> return (e, Success a)
            Nothing -> return (WQ writers, TryAgain)

-- |
-- Reads a value from a channel, replacing it with a different value.
-- Blocks until the replacement value is read, and then returns the old
-- value.
--
-- /CAUTION:/ This operation does not guarantee that the read and
-- subsequent write are atomic.  It is somewhat likely to be better
-- in that respect than 'readChan' followed by 'unGetChan', however.
swapChan :: Chan a -> a -> IO a
swapChan (Chan m) a' = join $ transactMVar m modify
  where
    modify e commit = case getWriters e of
      NoQ readers -> do
        message <- newEmptyMVar
        r       <- newIORef (Just message)
        _       <- commit (RQ (readers |> r))
        return $ do
          a <- takeMVar message `clear` r
          -- Race condition here!  I think we'd need a different
          -- representation to do this one right.
          writeChan (Chan m) a'
          return a
      (r, confirm) :< writers -> do
        maybea <- readIORef r
        case maybea of
          Just a  -> do
            r'       <- newIORef (Just a')
            confirm' <- newEmptyMVar
            _        <- mask $ \_ -> do
              putMVar confirm ()
              commit (WQ ((r', confirm') <| writers))
            return $ do
              takeMVar confirm' `clear` r'
              return a
          Nothing  -> do
            modify (WQ writers) commit

-- |
-- If a writer is available to synchronize with, synchronizes with the
-- writer, allowing its operation to complete, writes the replacement
-- value ahead of any other writers, and then returns immediately.
-- Unlike 'swapChan', guarantees that no other write can intervene.
tryAsyncSwapChan :: Chan a -> a -> IO (TryResult a)
tryAsyncSwapChan (Chan m) a' = tryModifyMVar m modify
  where
    modify e = case getWriters e of
      NoQ _ -> return (e, NotReady)
      (r, confirm) :< writers -> do
        maybea <- readIORef r
        case maybea of
          Just a  -> do
            r'       <- newIORef (Just a')
            confirm' <- newEmptyMVar
            putMVar confirm ()
            return (WQ ((r', confirm') <| writers), Success a)
          Nothing -> return (WQ writers, TryAgain)

-- | Is the channel currently empty?  Note that the answer may become
--   false arbitrarily soon.  Don't rely on this operation.
isEmptyChan :: Chan a -> IO Bool
isEmptyChan (Chan m) = do
  e <- readMVar m
  case getWriters e of
    NoQ _ -> return True
    _     -> return False

-- Helper for pulling getting all the waiting data in
-- a channel while discharging the writers.  Returns a (possibly
-- empty) queue of readers.
--
-- Rather complicated interface!  It takes a channel representation,
-- and maybe an integer bound on how much stuff to read.  It then
-- returns:
--  * The list of results,
--  * A queue of readers, possibly empty, and
--  * one of:
--     * The remaining list of writers, if the counter ran out, or
--     * The remaining counter, if the writers ran out.
getImmediateChanContents ::
  Rep a -> Maybe Integer ->
  IO ([a], Q (Reader a), Either (Q (Writer a)) (Maybe Integer))
getImmediateChanContents e0 n0 = case getWriters e0 of
  NoQ readers               ->
    return ([], readers, Right n0)
  ((r, confirm) :< writers) -> do
    loop n0 ((r, confirm) :< writers)
  where
    loop n        (NoQ ()) =
      return ([], empty, Right n)
    loop (Just 0) (writer :< writers) =
      return ([], empty, Left (writer <| writers))
    loop n        ((r, confirm) :< writers) = unsafeInterleaveIO $ do
      maybea <- readIORef r
      case maybea of
        Just a  -> do
          putMVar confirm ()
          (as, rs, rest) <- loop (fmap pred n) (dequeue () writers)
          return (a:as, rs, rest)
        Nothing ->
          loop n (dequeue () writers)

getChanMaybeN :: Chan a -> Maybe Integer -> IO [a]
getChanMaybeN (Chan m) n = modifyMVar m modify
  where
    modify e = do
      stopr               <- newIORef False
      (as, readers, rest) <- getImmediateChanContents e n
      case rest of
        Left writers -> return (WQ writers, as)
        Right n'     -> do
          readers'  <- makereaders n' stopr
          as'       <- loop stopr readers'
          return (RQ $ readers |>>> readers', as ++ as')
    loop _     []     = return []
    loop stopr (r:rs) = unsafeInterleaveIO $ do
      maybereader <- readIORef r
      case maybereader of
        Just reader -> do
          a  <- (readMVar reader `clear` r)
            `onException` writeIORef stopr True
          as <- loop stopr rs
          return (a:as)
        Nothing ->
          loop stopr rs
    makereaders (Just 0) _     = return []
    makereaders n'       stopr = unsafeInterleaveIO $ do
      stop    <- readIORef stopr
      if stop
        then return []
        else do
          message <- newEmptyMVar
          r       <- newIORef (Just message)
          rest    <- makereaders (fmap pred n') stopr
          return (r:rest)
-- |
-- Read the contents of the channel as a lazy list.  While this
-- operation returns immediately, forcing evaluation of the list will
-- block, which is why this is included among the blocking operations.
-- Writers will block until each link in the list is forced as well.
--
-- Any subsequent attempts to read from the channel will fail, unless
-- a thread is interrupted while blocking on forcing the list.  Don't
-- rely on this behavior.
getChanContents  :: Chan a -> IO [a]
getChanContents c = getChanMaybeN c Nothing

-- |
-- Read a given number of elements from the channel as a lazy list.
-- Like 'getChanContents', this operation returns immediately, but it
-- will block when the list is forced.  (Taking the length of the list
-- should block until all the matching writes complete.)
getChanN  :: Chan a -> Integer -> IO [a]
getChanN c = getChanMaybeN c . Just

-- |
-- Read the currently available elements from the channel as a lazy
-- list.  The list is lazy because the number of currently available
-- elements may be infinite (see 'writeList2Chan').
tryGetChanContents :: Chan a -> IO (TryResult [a])
tryGetChanContents (Chan m) = tryModifyMVar m modify
  where
    modify e = do
      (as, readers, _) <- getImmediateChanContents e Nothing
      return (RQ readers, Success as)

-- |
-- Read up to the given number of currently available elements
-- from the channel.  The list will be no longer than the given
-- number, but if there are insufficient writers available then
-- it may be shorter.  The writers will block until their portions
-- of the list's spine are forced.
tryGetChanN :: Chan a -> Integer -> IO (TryResult [a])
tryGetChanN (Chan m) n = tryModifyMVar m modify
  where
    modify e = do
      (as, readers, rest) <- getImmediateChanContents e (Just n)
      case rest of
        Left writers -> return (WQ writers, Success as)
        Right _      -> return (RQ readers, Success as)

genericWriteList2Chan :: Bool -> Chan a -> [a] -> IO ()
genericWriteList2Chan wait (Chan m) as0 = join $ modifyMVar m (loop as0)
  where
    loop []     e = return (e, return ())
    loop (a:as) e =
      case getReaders e of
        r :< readers -> do
          maybereader <- readIORef r
          case maybereader of
            Just reader -> do
              putMVar reader a
              loop as (RQ readers)
            Nothing ->
              loop (a:as) (RQ readers)
        NoQ writers -> do
          stopr      <- newIORef False
          writers'   <- makeWriters stopr (a:as)
          -- This seems like overkill, maybe, but it ensures that
          -- if the writer gets killed, the remainder of the list
          -- not yet delivered is dropped.
          let each (r, c) = do
                (takeMVar c `clear` r)
                  `onException` writeIORef stopr True
              action = if wait
                         then mapM_ each writers'
                         else return ()
          return (WQ (writers |>>> writers'), action)
    makeWriters _    []     = return []
    makeWriters stopr (a:as) = unsafeInterleaveIO $ do
      stop <- readIORef stopr
      if stop
        then return []
        else do
          rI       <- newIORef (Just a)
          confirmI <- newEmptyMVar
          rest     <- makeWriters stopr as
          return ((rI, confirmI):rest)

-- |
-- Write a list to a channel, blocking until the read completes.
-- It is guaranteed that no other writes can intervene among the
-- list elements.  (This cannot be implemented in terms of
-- 'writeChan'.)  The list may be infinite, in which case this
-- operation never completes.
--
-- Interrupting this operation before the list is read completely causes
-- the rest of the list not to be written.  (If you want to write the
-- whole list, 'asyncWriteList2Chan' may be suitable.)
writeList2Chan :: Chan a -> [a] -> IO ()
writeList2Chan = genericWriteList2Chan True

-- |
-- Write a list to a channel, succeeding immediately.  The list may
-- be infinite, in which case the operation still completes
-- immediately.  (Actually, it may take time proportional to the number
-- of readers that are ready, so if an infinite list is written to
-- 'getChanContents' on the other side, it may not actually complete.)
asyncWriteList2Chan :: Chan a -> [a] -> IO ()
asyncWriteList2Chan = genericWriteList2Chan False

-- |
-- Attempt to write as much of a list as possible to a channel
-- synchronously, but without blocking; returns the unwritten remainder
-- of the list.  This operation will write additional list elements so
-- long as -- there are readers ready to receive them (and so long as the
-- list doesn't run out).
tryWriteList2Chan :: Chan a -> [a] -> IO (TryResult (), [a])
tryWriteList2Chan (Chan m) as0 = do
  result <- tryModifyMVar m (loop as0)
  case result of
    Success pair -> return pair
    WouldBlock   -> return (WouldBlock, as0)
    TryAgain     -> return (TryAgain, as0)
    NotReady     -> return (NotReady, as0)
  where
    loop []     e = return (e, Success (Success (), []))
    loop (a:as) e = do
      case getReaders e of
        r :< readers -> mask $ \_ -> do
          maybereader <- readIORef r
          case maybereader of
            Just reader -> do
              putMVar reader a
              loop as (RQ readers)
            Nothing ->
              return (RQ readers, Success (TryAgain, a:as))
        NoQ _ -> return (e, Success (NotReady, a:as))

-- |
-- Lift results of the try* operations into 'Maybe'.  'Success' goes
-- to 'Just' and all kinds of failure go to 'Nothing'.
maybeTry :: IO (TryResult a) -> IO (Maybe a)
maybeTry io = do
  tr <- io
  return $ case tr of
    Success r -> Just r
    _         -> Nothing

---
--- Helpful MVar stuff
---

modifyMVar :: MVar a -> (a -> IO (a, b)) -> IO b
modifyMVar m io = mask $ \restore -> do
  a <- takeMVar m
  (a',b) <- restore (io a)
    `onException` putMVar m a
  putMVar m a'
  return b

-- Control.Concurrent.MVar doesn't have this, but it's pretty useful
-- for implementing non-blocking operations.
tryModifyMVar :: MVar a -> (a -> IO (a, TryResult b)) -> IO (TryResult b)
tryModifyMVar m io = mask $ \restore -> do
  maybea <- tryTakeMVar m
  case maybea of
    Just a -> do
      (a',b) <- restore (io a)
        `onException` putMVar m a
      putMVar m a'
      return b
    Nothing ->
      return WouldBlock

transactMVar :: MVar a ->
                (a -> (a -> IO ()) -> IO b) ->
                IO b
transactMVar m io = mask $ \restore -> do
  a <- takeMVar m
  r <- newIORef a
  restore (io a (writeIORef r))
    `finally` (readIORef r >>= putMVar m)

{-
tryTransactMVar :: MVar a ->
                   (a -> (a -> IO ()) -> IO (TryResult b)) ->
                   IO (TryResult b)
tryTransactMVar m io = mask $ \restore -> do
  maybea <- tryTakeMVar m
  case maybea of
    Just a -> do
      r <- newIORef a
      restore (io a (writeIORef r))
        `finally` (readIORef r >>= putMVar m)
    Nothing ->
      return WouldBlock
-}

