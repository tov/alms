module Util.Trace (
  TraceIndent, MonadTrace(..),
  traceN, trace, traceLow,
  debugLevel, debug,
  --
  TraceT(..), runTraceT, mapTraceT,
  --
  TraceMessage(..),
  TracePpr(..), TraceNesting(..),
) where

import Util
import Syntax.PprClass as Ppr

import Prelude ()
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

{-# INLINE debugLevel #-}
debugLevel ∷ Int
debugLevel = 0

{-# INLINE debug #-}
debug ∷ Bool
debug = debugLevel > 0

type TraceIndent = Int

class Monad m ⇒ MonadTrace m where
  getTraceIndent    ∷ m Int
  putTraceIndent    ∷ Int → m ()
  modifyTraceIndent ∷ (Int → Int) → m ()
  modifyTraceIndent f = getTraceIndent >>= putTraceIndent . f
  putTraceString    ∷ String → m ()
  putTraceString    = (return $!) . unsafePerformIO . putStr

class TraceMessage a where
  pprTrace        ∷ a → Doc
  pprTraceIndent  ∷ a → Ordering
  pprTraceIndent  = const EQ

{-# INLINE traceN #-}
traceN     ∷ (TraceMessage a, MonadTrace m) ⇒ Int → a → m ()
traceN     =
  if debug
    then \level →
      if debugLevel >= level
        then traceLow
        else \_ → return ()
    else \_ _ → return ()

{-# INLINE trace #-}
trace      ∷ (TraceMessage a, MonadTrace m) ⇒ a → m ()
trace      =
  if debug
    then traceLow
    else \_ → return ()

{-# INLINE traceLow #-}
traceLow   ∷ (TraceMessage a, MonadTrace m) ⇒ a → m ()
traceLow a = do
  n0 ← getTraceIndent
  (n, brace) ← case pprTraceIndent a of
    LT → putTraceIndent (n0 - 2) >> return (n0 - 2, (char '}' Ppr.<+>))
    EQ → return (n0, id)
    GT → putTraceIndent (n0 + 2) >> return (n0, (Ppr.<+> char '{'))
  let doc = nest n (brace (pprTrace a))
  putTraceString (show doc)
  putTraceString "\n"

---
--- MonadTrace instances
---

instance Monad m ⇒ MonadTrace (TraceT m) where
  putTraceIndent    = TraceT . put
  getTraceIndent    = TraceT get
  modifyTraceIndent = TraceT . modify

instance MonadTrace m ⇒ MonadTrace (ReaderT r m) where
  putTraceIndent    = lift . putTraceIndent
  getTraceIndent    = lift getTraceIndent
  modifyTraceIndent = lift . modifyTraceIndent

instance (MonadTrace m, Monoid w) ⇒ MonadTrace (WriterT w m) where
  putTraceIndent    = lift . putTraceIndent
  getTraceIndent    = lift getTraceIndent
  modifyTraceIndent = lift . modifyTraceIndent

instance MonadTrace m ⇒ MonadTrace (StateT s m) where
  putTraceIndent    = lift . putTraceIndent
  getTraceIndent    = lift getTraceIndent
  modifyTraceIndent = lift . modifyTraceIndent

instance (MonadTrace m, Monoid w) ⇒ MonadTrace (RWST r w s m) where
  putTraceIndent    = lift . putTraceIndent
  getTraceIndent    = lift getTraceIndent
  modifyTraceIndent = lift . modifyTraceIndent

instance MonadTrace m ⇒ MonadTrace (ListT m) where
  putTraceIndent    = lift . putTraceIndent
  getTraceIndent    = lift getTraceIndent
  modifyTraceIndent = lift . modifyTraceIndent

---
--- A transformer
---

newtype TraceT m a = TraceT { unTraceT ∷ StateT TraceIndent m a }
  deriving (Functor, Applicative, Monad, MonadTrans)

runTraceT ∷ Monad m ⇒ TraceT m a → m a
runTraceT = flip evalStateT 0 . unTraceT

mapTraceT   ∷ Monad m ⇒
              (m a → m b) → TraceT m a → TraceT m b
mapTraceT f = TraceT . mapStateT f' . unTraceT where
  f' ma = do
    (a, indent) ← ma
    b ← f (return a)
    return (b, indent)

instance MonadReader r m ⇒ MonadReader r (TraceT m) where
  ask   = lift ask
  local = mapTraceT . local

instance MonadWriter w m ⇒ MonadWriter w (TraceT m) where
  tell   = lift . tell
  listen = mapTraceT listen
  pass   = mapTraceT pass

instance MonadState s m ⇒ MonadState s (TraceT m) where
  get    = lift get
  put    = lift . put

instance MonadIO m ⇒ MonadIO (TraceT m) where
  liftIO = lift . liftIO

---
--- An instance for IO
---

{-# NOINLINE ioTraceIndent #-}
ioTraceIndent ∷ IORef TraceIndent
ioTraceIndent = unsafePerformIO (newIORef 0)

instance MonadTrace IO where
  getTraceIndent    = readIORef ioTraceIndent
  putTraceIndent    = writeIORef ioTraceIndent
  modifyTraceIndent = modifyIORef ioTraceIndent
  putTraceString    = putStr

---
--- TraceMessage instances
---

newtype TracePpr a = TracePpr { unTracePpr ∷ a }

instance Ppr a ⇒ TraceMessage (TracePpr a) where
  pprTrace     = ppr . unTracePpr

instance TraceMessage Doc where pprTrace = id

data TraceNesting a
  = TraceIn  { unTraceNesting ∷ !a }
  | TraceOut { unTraceNesting ∷ !a }

instance TraceMessage String where
  pprTrace       = Ppr.text . snd . pprDecomposeString
  pprTraceIndent = fst . pprDecomposeString

pprDecomposeString ∷ String → (Ordering, String)
pprDecomposeString ('}':s) = (LT, dropWhile (== ' ') s)
pprDecomposeString s       = case reverse s of
  '{':s' → (GT, reverse (dropWhile (== ' ') s'))
  _      → (EQ, s)

instance TraceMessage a ⇒ TraceMessage (TraceNesting a) where
  pprTrace = pprTrace . unTraceNesting
  pprTraceIndent (TraceIn _)  = GT
  pprTraceIndent (TraceOut _) = LT

instance (Ppr a, Ppr z)
       ⇒ TraceMessage (a,z) where
  pprTrace (a,z) = ppr a <> char '(' <> ppr z <> char ')'

instance (Ppr a, Ppr b, Ppr z)
       ⇒ TraceMessage (a,b,z) where
  pprTrace (a,b,z) =
    hang
      (ppr a <> char '(' <> p b)
      4
      (fsep
       [
        ppr z <> char ')'])

instance (Ppr a, Ppr b, Ppr c, Ppr z)
       ⇒ TraceMessage (a,b,c,z) where
  pprTrace (a,b,c,z) =
    hang
      (ppr a <> char '(' <> p b)
      4
      (fsep
       [p c,
        ppr z <> char ')'])

instance (Ppr a, Ppr b, Ppr c, Ppr d, Ppr z)
       ⇒ TraceMessage (a,b,c,d,z) where
  pprTrace (a,b,c,d,z) =
    hang
      (ppr a <> char '(' <> p b)
      4
      (fsep
       [p c, p d,
        ppr z <> char ')'])

instance (Ppr a, Ppr b, Ppr c, Ppr d, Ppr e, Ppr z)
       ⇒ TraceMessage (a,b,c,d,e,z) where
  pprTrace (a,b,c,d,e,z) =
    hang
      (ppr a <> char '(' <> p b)
      4
      (fsep
       [p c, p d, p e,
        ppr z <> char ')'])

instance (Ppr a, Ppr b, Ppr c, Ppr d, Ppr e, Ppr f, Ppr z)
       ⇒ TraceMessage (a,b,c,d,e,f,z) where
  pprTrace (a,b,c,d,e,f,z) =
    hang
      (ppr a <> char '(' <> p b)
      4
      (fsep
       [p c, p d, p e, p f,
        ppr z <> char ')'])

instance (Ppr a, Ppr b, Ppr c, Ppr d, Ppr e, Ppr f, Ppr g, Ppr z)
       ⇒ TraceMessage (a,b,c,d,e,f,g,z) where
  pprTrace (a,b,c,d,e,f,g,z) =
    hang
      (ppr a <> char '(' <> p b)
      4
      (fsep
       [p c, p d, p e, p f, p g,
        ppr z <> char ')'])

instance (Ppr a, Ppr b, Ppr c, Ppr d, Ppr e, Ppr f, Ppr g, Ppr h, Ppr z)
       ⇒ TraceMessage (a,b,c,d,e,f,g,h,z) where
  pprTrace (a,b,c,d,e,f,g,h,z) =
    hang
      (ppr a <> char '(' <> p b)
      4
      (fsep
       [p c, p d, p e, p f, p g, p h,
        ppr z <> char ')'])

instance (Ppr a, Ppr b, Ppr c, Ppr d, Ppr e, Ppr f, Ppr g, Ppr h, Ppr i, Ppr z)
       ⇒ TraceMessage (a, b, c, d, e, f, g, h, i, z) where
  pprTrace (a,b,c,d,e,f,g,h,i,z) =
    hang
      (ppr a <> char '(' <> p b)
      4
      (fsep
       [p c, p d, p e, p f, p g, p h, p i,
        ppr z <> char ')'])

-- Very common helper
p :: Ppr a => a -> Doc
p x = ppr x <> char ';'
