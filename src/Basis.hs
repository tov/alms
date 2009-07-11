{-#
  OPTIONS_GHC -fno-warn-orphans
  #-}
{-#
  LANGUAGE DeriveDataTypeable
  #-}
module Basis (
  primBasis, srcBasis, basis2venv, basis2tenv
) where

import Util
import BasisUtils
import Dynamics
import Ppr (text)
import Syntax

import Basis.Channels

import IO (hFlush, stdout)
import Data.IORef (IORef, newIORef, readIORef, writeIORef, atomicModifyIORef)
import Data.Typeable
import qualified Control.Concurrent as CC
import qualified Control.Concurrent.MVar as MV
import Control.Monad
import Control.Monad.Fix

primBasis :: [Entry]
primBasis  = [
    ---
    --- Ordinary constants:
    ---

    --- name    -:  ctype  -: atype  -= value
    --- name    -:: *type            -= value

    -- Primitive types:
    -- "unit" built in
    -- "bool" built in
    "int"    `primtype` tdInt,
    "string" `primtype` tdString,

    "*"    `primtype` tdTuple,
    "->"   `primtype` tdArr,
    "-o"   `primtype` tdLol,

    -- Sums
    typeC "'a option = None | Some of 'a",
    typeC "('a, 'b) either = Left of 'a | Right of 'b",

    typeA "'<a option = None | Some of '<a",
    typeA "('<a, '<b) either = Left of '<a | Right of '<b",

    -- Recursion
    pfun 2 "fix" -:: "all 'a 'b. (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)"
      -= (\(VaFun _ f) -> mfix f),

    -- Lists
    typeC "'a list  = Nil | Cons of 'a * 'a list",
    typeA "'<a list = Nil | Cons of '<a * '<a list",

    -- Arithmetic
    binArith "add" (+),
    binArith "sub" (-),
    binArith "mul" (*),
    binArith "div" div,
    fun "le" -:: "int -> int -> bool"
      -= ((<=) :: Integer -> Integer -> Bool),

    -- Strings
    fun "explode"  -:: "string -> int list"
      -= map char2integer,
    fun "implode"  -:: "int list -> string"
      -= map integer2char,
    pfun 1 "toString" -:: "all 'a. 'a -> string"
      -= (return . show :: Value -> IO String),

    -- "Magic" equality and print; failure
    pfun 1 "eq" -:: "all 'a. 'a -> 'a -> bool"
      -= ((==) :: Value -> Value -> Bool),
    pfun 1 "print" -:: "all 'a. 'a -> unit"
      -= (print :: Value -> IO ()),
    pfun 1 "failwith" -: "all 'a. string -> 'a"
                      -: "all '<a. string -> '<a"
      -= (fail . ("Failure: "++) :: String -> IO Value),

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
    typeC "'a ref",
    typeA "'a ref qualifier A",
    pfun 1 "ref" -: "all 'a. 'a -> 'a ref"
                 -: "all '<a. '<a -> '<a ref"
      -= (\v -> Ref `fmap` newIORef v),
    pfun 2 "swap" -: ""
                  -: "all '<a '<b. '<a ref * '<b -> '<b ref * '<a"
      -= (\(vr, v1) -> do
            v0 <- atomicModifyIORef (unRef vr) (\v0 -> (v1, v0))
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
    typeA "thread qualifier A",
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
    typeA "+'a future qualifier A",
    typeA "-'a cofuture qualifier A",
    pfun 1 "newFuture" -: ""
                       -: "all '<a. (unit -o '<a) -> '<a future"
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f () >>= MV.putMVar future)
            return (Future future),
    pfun 1 "getFuture" -: ""
                       -: "all '<a. '<a future -> '<a"
      -= (MV.takeMVar . unFuture),
    pfun 1 "newCofuture" -: ""
                         -: "all '<a. ('<a future -o unit) -> '<a cofuture"
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f (Future future) >> return ())
            return (Future future),
    pfun 1 "putCofuture" -: ""
                         -: "all '<a. '<a cofuture -> '<a -o unit"
      -= \future value -> MV.putMVar (unFuture future) value,

    -- Session-typed channels
    typeA "'a rendezvous",
    typeA "+'a channel qualifier A",
    -- Unfortunately, we need these types to be primitive in order to
    -- compute duals.
    "dual"   `primtype` tdDual,
    "send"   `primtype` tdSend,
    "recv"   `primtype` tdRecv,
    "select" `primtype` tdSelect,
    "follow" `primtype` tdFollow,
    pfun 1 "newRendezvous" -: ""
                           -: "all 's. unit -> 's rendezvous"
      -= \() -> do
           mv <- newChan
           return (Rendezvous mv),
    pfun 1 "request" -: ""
                     -: "all 's. 's rendezvous -> 's channel"
      -= \rv -> do
           readChan (unRendezvous rv),
    pfun 1 "accept" -: ""
                    -: "all 's. 's rendezvous -> 's dual channel"
      -= \rv -> do
           c <- Channel `fmap` newChan
           writeChan (unRendezvous rv) c
           return c,
    pfun 2 "send"
      -: ""
      -: "all '<a 's. ('<a send -> 's) channel -> '<a -o 's channel"
      -= \c a -> do
           writeChan (unChannel c) a
           return c,
    pfun 2 "recv"
      -: ""
      -: "all '<a 's. ('<a recv -> 's) channel -> '<a * 's channel"
      -= \c -> do
           a <- readChan (unChannel c)
           return (a, c),
    pfun 2 "sel1"
      -: ""
      -: "all 's1 's2. ('s1 * 's2) select channel -> 's1 channel"
      -= \c -> do
           writeChan (unChannel c) (vinj True)
           return c,
    pfun 2 "sel2"
      -: ""
      -: "all 's1 's2. ('s1 * 's2) select channel -> 's2 channel"
      -= \c -> do
           writeChan (unChannel c) (vinj False)
           return c,
    pfun 2 "follow"
      -: ""
      -: ("all 's1 's2. ('s1 * 's2) follow channel -> " ++
                       "('s1 channel, 's2 channel) either")
      -= \c -> do
           e  <- readChan (unChannel c)
           e' <- vprjM e
           if e'
             then return (Left c)
             else return (Right c),

    -- Unsafe coercions
    pfun 2 "unsafeCoerce" -:: "all '<b '<a. '<a -> '<b"
      -= (id :: Value -> Value),

    -- Used by contract system -- # names prevent them from appearing
    -- in a source program (which could result in nasty shadowing)
    pfun 1 "#ref" -:: "all 'a. 'a -> 'a ref"
      -= (\v -> Ref `fmap` newIORef v),
    pfun 1 "#modify" -:: "all 'a. 'a ref * 'a -> 'a"
      -= (\(vr, v1) -> do
            atomicModifyIORef (unRef vr) (\v0 -> (v1, v0))),
    fun "#blame" -: "string -> string -> unit"
                 -: ""
      -= \who what -> fail $ "Contract violation: " ++
                             who ++ ": " ++
                             what :: IO ()
  ]

newtype Ref = Ref { unRef :: IORef Value }
  deriving (Eq, Typeable)

instance Valuable Ref where
  veq = (==)
  vpprPrec _ _ = text "#<ref>"

newtype Future = Future { unFuture :: MV.MVar Value }
  deriving (Eq, Typeable)

instance Valuable Future where
  veq = (==)
  vpprPrec _ _ = text "#<(co)future>"

newtype Channel = Channel { unChannel :: Chan Value }
  deriving (Eq, Typeable)

instance Valuable Channel where
  veq = (==)
  vpprPrec _ _ = text "#<channel>"

newtype Rendezvous = Rendezvous { unRendezvous :: Chan Channel }
  deriving (Eq, Typeable)

instance Valuable Rendezvous where
  veq = (==)
  vpprPrec _ _ = text "#<rendezvous>"

srcBasis :: String
srcBasis  = unlines [
  "module[C] null = ^'a (x : 'a list).",
  "  match x with",
  "  | Nil -> true",
  "  | _   -> false",
  "module[C] hd = ^'a (xs : 'a list).",
  "  let Cons(x, _) = xs in x",
  "module[C] tl = ^'a (xs : 'a list).",
  "  let Cons(_, xs') = xs in xs'",
  "module[A] anull = ^'<a (xs : '<a list).",
  "  match xs with",
  "  | Nil          -> (Nil['<a], true)",
  "  | Cons(x, xs') -> (Cons(x, xs'), false)",
  "",
  "module[C] foldrC =",
  "  let rec foldr 'a 'b (f : 'a -> 'b -> 'b)",
  "                      (z : 'b) (xs : 'a list) : 'b =",
  "        match xs with",
  "        | Nil -> z",
  "        | Cons(x,xs) -> f x (foldr f z xs)",
  "   in foldr",
  "module[A] foldrA =",
  "  let rec foldr '<a '<b (f : '<a -> '<b -o '<b)",
  "                        (z : '<b) |(xs : '<a list) : '<b =",
  "        match xs with",
  "        | Nil -> z",
  "        | Cons(x,xs) -> f x (foldr f z xs)",
  "   in foldr",
  "module[C] alist2clist : all 'a. {{'a} list} -> 'a list =",
  "  ^'a. foldrA (^(x:'a) (xs:'a list). Cons(x, xs)) Nil['a]",
  "module[A] clist2alist : all 'a. {{'a} list} -> 'a list =",
  "  ^'a. foldrC (^(x:'a) (xs:'a list). Cons(x, xs)) Nil['a]",
  ""
  ]
