{-#
  OPTIONS_GHC -fno-warn-orphans
  #-}
{-#
  LANGUAGE DeriveDataTypeable
  #-}
module Basis (
  basis, basis2venv, basis2tenv
) where

import Util
import BasisUtils
import Dynamics
import Ppr (text)

import IO (hFlush, stdout)
import Data.IORef (IORef, newIORef, readIORef, writeIORef, atomicModifyIORef)
import Data.Typeable
import qualified Control.Concurrent as CC
import qualified Control.Concurrent.MVar as MV
import Control.Monad
import Control.Monad.Fix

basis :: [Entry]
basis  = [
    ---
    --- Special (untypable) constants:
    ---

    val "()"  -:: "" -= (),

    ---
    --- Ordinary constants:
    ---

    --- name    -:  ctype  -: atype   -= value
    --- name    -:: *type            -= value

    -- Booleans
    val "true"  -:: "bool" -= True,
    val "false" -:: "bool" -= False,

    -- Recursion
    pfun 2 "fix" -:: "all 'a 'b. (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)"
      -= (\(VaFun _ f) -> mfix f),

    -- "Magic" equality and print:
    pfun 1 "eq" -:: "all 'a. 'a -> 'a -> bool"
      -= ((==) :: Value -> Value -> Bool),
    pfun 1 "print" -:: "all 'a. 'a -> unit"
      -= (print :: Value -> IO ()),

    -- Arithmetic
    binArith "add" (+),
    binArith "sub" (-),
    binArith "mul" (*),
    binArith "div" div,
    fun "le" -:: "int -> int -> bool"
      -= ((<=) :: Integer -> Integer -> Bool),

    pval 1 "nil"  -: "all 'a. 'a list"
                  -: "all '<a. '<a list"
      -= ([] :: [Value]),
    pfun 1 "cons" -: "all 'a. 'a -> 'a list -> 'a list"
                  -: "all '<a. '<a -> '<a list -> '<a list"
      -= ((:) :: Value -> [Value] -> [Value]),
    pfun 1 "null" -:: "all 'a. 'a list -> bool"
      -= (null :: [Value] -> Bool),
    pfun 1 "hd"   -:: "all 'a. 'a list -> 'a"
      -= (head :: [Value] -> Value),
    pfun 1 "tl"   -:: "all 'a. 'a list -> 'a list"
      -= (tail :: [Value] -> [Value]),
    pfun 1 "uncons" -: "all 'a. 'a list -> 'a * 'a list"
                    -: "all '<a. '<a list -> '<a * '<a list"
      -= (liftM2 (,) head tail :: [Value] -> (Value, [Value])),
    pfun 1 "anull" -: ""
                   -: "all '<a. '<a list -> '<a list * bool"
      -= (liftM2 (,) id null :: [Value] -> ([Value], Bool)),

    -- Strings
    fun "explode"  -:: "string -> int list"
      -= map (vinj . char2integer),
    fun "implode"  -:: "int list -> string"
      -= vinj . map (integer2char . vprj),
    pfun 1 "toString" -:: "all 'a. 'a -> string"
      -= (return . show :: Value -> IO String),

    -- I/O
    fun "putChar"  -:: "int -> unit"
      -= putChar . integer2char,
    fun "getChar"  -:: "unit -> int"
      -= \() -> fmap char2integer getChar,
    fun "flush"    -:: "unit -> unit"
      -= \() -> hFlush stdout,
    fun "putStr"   -:: "string -> unit"
      -= putStr,
    fun "putStrLn" -:: "string -> unit"
      -= putStrLn,
    fun "getLine"  -:: "unit -> string"
      -= \() -> getLine,

    -- References
    pfun 1 "ref" -: "all 'a. 'a -> 'a ref"
                 -: "all '<a. '<a -> '<a ref"
      -= (\v -> Ref `fmap` newIORef v),
    pfun 2 "swap" -: ""
                  -: "all '<a '<b. '<a ref * '<b -> '<b ref * '<a"
      -= (\(vr, v1) -> do
            v0 <- atomicModifyIORef (unRef (vprj vr)) (\v0 -> (v1, v0))
            return (vr, v0)),
    pfun 1 "takeRef" -: "all 'a. 'a ref -> 'a"
                     -: "all '<a. '<a ref -> '<a"
      -= (\r -> readIORef (unRef r)),
    pfun 1 "readRef" -:: "all 'a. 'a ref -> 'a ref * 'a"
      -= (\r -> do
           v <- readIORef (unRef r)
           return (r, v)),
    pfun 1 "writeRef" -: "all 'a. 'a ref -> 'a -> 'a ref"
                      -: "all '<a. '<a ref -> '<a -o '<a ref"
      -= (\r v -> do
           writeIORef (unRef r) v
           return r),

    -- Threads
    fun "threadFork" -: ""
                     -: "(unit -o unit) -> thread"
      -= \f -> Vinj `fmap` CC.forkIO (vapp f () >> return ()),
    fun "threadKill" -: ""
                     -: "thread -> unit"
      -= CC.killThread . unVinj,
    fun "threadDelay" -:: "int -> unit"
      -= CC.threadDelay . (fromIntegral :: Integer -> Int),
    fun "printThread" -: ""
                      -: "thread -> thread"
      -= \t -> do print (t :: Vinj CC.ThreadId); return t,

    -- Futures
    pfun 1 "newFuture" -: ""
                       -: "all '<a. (unit -o '<a) -> '<a future"
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f () >>= MV.putMVar future)
            return (MVar future),
    pfun 1 "getFuture" -: ""
                       -: "all '<a. '<a future -> '<a"
      -= (MV.takeMVar . unMVar),
    pfun 1 "newCofuture" -: ""
                         -: "all '<a. ('<a future -o unit) -> '<a cofuture"
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f (MVar future) >> return ())
            return (MVar future),
    pfun 1 "putCofuture" -: ""
                         -: "all '<a. '<a cofuture -> '<a -o unit"
      -= \future value -> MV.putMVar (unMVar future) value,

    -- Used by contract system -- # names prevent them from appearing
    -- in a source program (which could result in nasty shadowing)
    pfun 1 "#ref" -:: "all 'a. 'a -> 'a ref"
      -= (\v -> Ref `fmap` newIORef v),
    pfun 1 "#modify" -:: "all 'a. 'a ref * 'a -> 'a"
      -= (\(vr, v1) -> do
            atomicModifyIORef (unRef (vprj vr)) (\v0 -> (v1, v0))),
    fun "#blame" -: "string -> string -> unit"
                 -: ""
      -= \who what -> fail $ "Contract violation: " ++
                             who ++ ": " ++
                             what :: IO ()
  ]

-- For references (and printing them)
newtype Ref = Ref { unRef :: IORef Value }
  deriving (Eq, Typeable)

instance Valuable Ref where
  veq = (==)
  vpprPrec _ _ = text "#<ref>"

newtype MVar = MVar { unMVar :: MV.MVar Value }
  deriving (Eq, Typeable)

instance Valuable MVar where
  veq = (==)
  vpprPrec _ _ = text "#<(co)future>"

