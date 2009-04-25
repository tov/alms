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
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef)
import Data.Typeable
import qualified Control.Concurrent as CC
import qualified Control.Concurrent.MVar as MV

basis :: [Entry]
basis  = [
    ---
    --- Special (untypable) constants:
    ---

    val "()"  -:: "" -= (),
    fun "ref" -:: ""
      -= (\v -> Ref `fmap` newIORef v),
    fun "swap" -:: ""
      -= (\(vr, v1) -> do
            v0 <- atomicModifyIORef (unRef (vprj vr)) (\v0 -> (v1, v0))
            return (vr, v0)),
    fun "readRef" -:: ""
      -= readIORef . unRef,

    fun "newFuture" -:: ""    -- (unit -o 'a) -> 'a future
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f () >>= MV.putMVar future)
            return (MVar future),
    fun "getFuture" -:: ""    -- 'a future -> 'a
      -= MV.takeMVar . unMVar,
    fun "newCofuture" -:: ""  -- ('a future -o unit) -> 'a cofuture
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f (MVar future) >> return ())
            return (MVar future),
    fun "putCofuture" -:: ""  -- 'a cofuture -> 'a -o unit
      -= \future value -> MV.putMVar (unMVar future) value,
    fun "coroutine"   -:: ""  -- ('a future * 'b cofuture -o unit)
                              -- -> 'b future * 'a cofuture
      -= \f -> do
           a <- MV.newEmptyMVar
           b <- MV.newEmptyMVar
           CC.forkIO (vapp f (MVar a, MVar b) >> return ())
           return (MVar b, MVar a),

    ---
    --- Ordinary constants:
    ---

    --- name    -:  ctype  -: atype   -= value
    --- name    -:: *type            -= value
    val "true"  -:: "bool" -= True,
    val "false" -:: "bool" -= False,

    binArith "add" (+),
    binArith "sub" (-),
    binArith "mul" (*),
    binArith "div" div,
    fun "le" -: "int -> int -> bool"
             -: "int -> int -> bool"
      -= ((<=) :: Integer -> Integer -> Bool),

    val "nil"  -:: "int list" -= ([] :: [Value]),
    fun "cons" -:: "int -> int list -> int list"
      -= ((:) :: Value -> [Value] -> [Value]),
    fun "null" -:: "int list -> bool"
      -= (null :: [Value] -> Bool),
    fun "hd"   -:: "int list -> int"
      -= (head :: [Value] -> Value),
    fun "tl"   -:: "int list -> int list"
      -= (tail :: [Value] -> [Value]),

    fun "printInt" -:: "int -> unit"
      -= (print :: Integer -> IO ()),
    fun "printStr" -:: "string -> unit"
      -= (print :: Value -> IO ()),
    fun "putChar"  -:: "int -> unit"
      -= putChar . integer2char,
    fun "getChar"  -:: "unit -> int"
      -= \() -> fmap char2integer getChar,
    fun "flush"    -:: "unit -> unit"
      -= \() -> hFlush stdout,

    fun "eqStr"    -:: "string -> string -> bool"
      -= ((==) :: String -> String -> Bool),
    fun "putStr"   -:: "string -> unit"
      -= putStr,
    fun "putStrLn" -:: "string -> unit"
      -= putStrLn,
    fun "getLine"  -:: "unit -> string"
      -= \() -> getLine,
    fun "explode"  -:: "string -> int list"
      -= map (vinj . char2integer),
    fun "implode"  -:: "int list -> string"
      -= vinj . map (integer2char . vprj),

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

