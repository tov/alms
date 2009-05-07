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

    -- "Magic" equality and print:
    fun "eq" -:: "all 'a. 'a -> 'a -> bool"
      -= tabs ((==) :: Value -> Value -> Bool),
    fun "print" -:: "all 'a. 'a -> unit"
      -= tabs (print :: Value -> IO ()),

    -- Arithmetic
    binArith "add" (+),
    binArith "sub" (-),
    binArith "mul" (*),
    binArith "div" div,
    fun "le" -:: "int -> int -> bool"
      -= ((<=) :: Integer -> Integer -> Bool),

    fun "nil"  -: "all 'a. 'a list"
               -: "all '<a. '<a list"
      -= tabs ([] :: [Value]),
    fun "cons" -: "all 'a. 'a -> 'a list -> 'a list"
               -: "all '<a. '<a -> '<a list -> '<a list"
      -= tabs ((:) :: Value -> [Value] -> [Value]),
    fun "null" -:: "all 'a. 'a list -> bool"
      -= tabs (null :: [Value] -> Bool),
    fun "hd"   -:: "all 'a. 'a list -> 'a"
      -= tabs (head :: [Value] -> Value),
    fun "tl"   -:: "all 'a. 'a list -> 'a list"
      -= tabs (tail :: [Value] -> [Value]),
    fun "uncons" -: "all 'a. 'a list -> 'a * 'a list"
                 -: "all '<a. '<a list -> '<a * '<a list"
      -= tabs (liftM2 (,) head tail :: [Value] -> (Value, [Value])),
    fun "anull" -: ""
                -: "all '<a. '<a list -> '<a list * bool"
      -= tabs (liftM2 (,) id null :: [Value] -> ([Value], Bool)),

    -- Strings
    fun "explode"  -:: "string -> int list"
      -= map (vinj . char2integer),
    fun "implode"  -:: "int list -> string"
      -= vinj . map (integer2char . vprj),
    fun "toString" -:: "all 'a. 'a -> string"
      -= tabs (return . show :: Value -> IO String),

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
    fun "ref" -: "all 'a. 'a -> 'a ref"
              -: "all '<a. '<a -> '<a ref"
      -= tabs (\v -> Ref `fmap` newIORef v),
    fun "swap" -: ""
               -: "all '<a '<b. '<a ref * '<b -> '<b ref * '<a"
      -= tabs.tabs $ (\(vr, v1) -> do
            v0 <- atomicModifyIORef (unRef (vprj vr)) (\v0 -> (v1, v0))
            return (vr, v0)),
    fun "takeRef" -: "all 'a. 'a ref -> 'a"
                  -: "all '<a. '<a ref -> '<a"
      -= tabs (\r -> readIORef (unRef r)),
    fun "readRef" -:: "all 'a. 'a ref -> 'a ref * 'a"
      -= tabs (\r -> do
           v <- readIORef (unRef r)
           return (r, v)),
    fun "writeRef" -: "all 'a. 'a ref -> 'a -> 'a ref"
                   -: "all '<a. '<a ref -> '<a -o '<a ref"
      -= tabs (\r v -> do
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
    fun "newFuture" -: ""
                    -: "all '<a. (unit -o '<a) -> '<a future"
      -= \() f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f () >>= MV.putMVar future)
            return (MVar future),
    fun "getFuture" -: ""
                    -: "all '<a. '<a future -> '<a"
      -= (\() m -> MV.takeMVar (unMVar m)),
    fun "newCofuture" -: ""
                      -: "all '<a. ('<a future -o unit) -> '<a cofuture"
      -= \() f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f (MVar future) >> return ())
            return (MVar future),
    fun "putCofuture" -: ""
                      -: "all '<a. '<a cofuture -> '<a -o unit"
      -= \() future value -> MV.putMVar (unMVar future) value,

    -- Used by contract system -- # names prevent them from appearing
    -- in a source program (which could result in nasty shadowing)
    fun "#ref" -:: "all 'a. 'a -> 'a ref"
      -= tabs (\v -> Ref `fmap` newIORef v),
    fun "#modify" -:: "all 'a. 'a ref * 'a -> 'a"
      -= tabs $ (\(vr, v1) -> do
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

