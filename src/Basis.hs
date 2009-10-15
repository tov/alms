{-#
  LANGUAGE DeriveDataTypeable
  #-}
module Basis (
  primBasis, srcBasis, basis2venv, basis2tenv
) where

import Util
import BasisUtils
import Value (Valuable(..), Value(..), Vinj(..))
import Ppr (text)
import Syntax

import Basis.Channels
import qualified Basis.IO
import qualified Basis.Socket
import qualified Basis.Exn

import qualified IO
import qualified System.Environment as Env
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef)
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
    typeT "any  = all '<a. '<a",
    typeT "bool = false | true",
    "int"    `primtype` tdInt,
    typeT "char = int",
    "float"  `primtype` tdFloat,
    "string" `primtype` tdString,

    "*"    `primtype` tdTuple,
    "->"   `primtype` tdArr,
    "-o"   `primtype` tdLol,

    -- Sums
    typeT "'<a option = None | Some of '<a",
    typeT "('<a, '<b) either = Left of '<a | Right of '<b",

    -- Recursion
    pfun 2 "fix" -:: "all 'a 'b. (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)"
      -= (\(VaFun _ f) -> mfix f),

    -- Lists
    typeT "'<a list = Nil | Cons of '<a * '<a list",

    -- Arithmetic
    binArith "+" (+),
    binArith "-" (-),
    binArith "*" (*),
    binArith "/" div,
    binArith "%" mod,
    fun "abs" -:: "int -> int"
      -= (abs :: Integer -> Integer),
    fun "<=" -:: "int -> int -> bool"
      -= ((<=) :: Integer -> Integer -> Bool),

    -- Floating point arithmetic
    fun "<=." -:: "float -> float -> bool"
      -= ((<=) :: Double -> Double -> Bool),
    fun "<." -:: "float -> float -> bool"
      -= ((<) :: Double -> Double -> Bool),
    fun "+." -:: "float -> float -> float"
      -= ((+) :: Double -> Double -> Double),
    fun "-." -:: "float -> float -> float"
      -= ((-) :: Double -> Double -> Double),
    fun "*." -:: "float -> float -> float"
      -= ((*) :: Double -> Double -> Double),
    fun "/." -:: "float -> float -> float"
      -= ((/) :: Double -> Double -> Double),
    fun "**" -:: "float -> float -> float"
      -= ((**) :: Double -> Double -> Double),
    fun "sqrt" -:: "float -> float"
      -= (sqrt :: Double -> Double),
    fun "log" -:: "float -> float"
      -= (log :: Double -> Double),
    fun "absf" -:: "float -> float"
      -= (abs :: Double -> Double),
    fun "float_of_int" -:: "int -> float"
      -= (fromIntegral :: Integer -> Double),
    fun "int_of_float" -:: "float -> int"
      -= (round :: Double -> Integer),
    fun "string_of_float" -:: "float -> string"
      -= (show :: Double -> String),
    fun "float_of_string" -:: "string -> float"
      -= (read :: String -> Double),
    fun "string_of_int" -:: "int -> string"
      -= (show :: Integer -> String),
    fun "int_of_string" -:: "string -> int"
      -= (read :: String -> Integer),

    -- Strings
    fun "explode"  -:: "string -> int list"
      -= map char2integer,
    fun "implode"  -:: "int list -> string"
      -= map integer2char,
    fun "^" -:: "string -> string -> string"
      -= ((++) :: String -> String -> String),
    pfun 1 "string_of" -:: "all 'a. 'a -> string"
      -= (return . show :: Value -> IO String),
    fun "string_length" -:: "string -> int"
      -= \s -> toInteger (length (s :: String)),

    -- "Magic" equality and print; failure
    pfun 1 "==" -:: "all 'a. 'a -> 'a -> bool"
      -= ((==) :: Value -> Value -> Bool),
    pfun 1 "print" -:: "all 'a. 'a -> unit"
      -= (print :: Value -> IO ()),

    -- I/O
    fun "putChar"  -:: "int -> unit"
      -= putChar . integer2char,
    fun "getChar"  -:: "unit -> int"
      -= \() -> fmap char2integer getChar,
    fun "flush"    -:: "unit -> unit"
      -= \() -> IO.hFlush IO.stdout,
    fun "putStr"   -:: "string -> unit"
      -= putStr,
    fun "putStrLn" -:: "string -> unit"
      -= putStrLn,
    fun "getLine"  -:: "unit -> string"
      -= \() -> getLine,

    -- The environment
    fun "getArgs" -:: "unit -> string list"
      -= \() -> Env.getArgs,
    fun "getProgName" -:: "unit -> string"
      -= \() -> Env.getProgName,
    fun "getEnv" -:: "string -> string"
      -= Env.getEnv,
    fun "getEnvironment" -:: "unit -> (string * string) list"
      -= \() -> Env.getEnvironment,

    -- References
    typeC "'a ref",
    typeA "'<a ref qualifier U",
    typeA "'<a aref qualifier A",
    pfun 1 "ref" -: "all 'a. 'a -> 'a ref"
                 -: "all '<a. '<a -> '<a ref"
      -= (\v -> Ref `fmap` newIORef v),
    pfun 1 "aref" -: ""
                  -: "all '<a. '<a -> '<a aref"
      -= (\v -> Ref `fmap` newIORef v),

    pfun 1 "!" -: "all 'a. 'a ref -> 'a"
               -: "all 'a. 'a ref -> 'a"
      -= (\r -> readIORef (unRef r)),
    pfun 1 "!!" -: ""
                -: "all 'a. 'a aref -> 'a aref * 'a"
      -= (\r -> do
           v <- readIORef (unRef r)
           return (r, v)),
    pfun 1 "<-" -: "all 'a. 'a ref -> 'a -> 'a"
                -: "all '<a. '<a ref -> '<a -o '<a"
      -= (\r v -> do
           atomicModifyIORef (unRef r) (\v' -> (v, v'))),
    pfun 1 "<-!" -: ""
                 -: "all '<a '<b. '<a aref -> '<b -o '<b aref * '<a"
      -= (\r v -> do
           atomicModifyIORef (unRef r) (\v' -> (v, (r, v')))),

    submod "Future" [
      -- Futures
      typeA "+'a future qualifier A",
      typeA "-'a cofuture qualifier A",

      pfun 1 "new" -: ""
                   -: "all '<a. (unit -o '<a) -> '<a future"
        -= \f -> do
              future <- MV.newEmptyMVar
              CC.forkIO (vapp f () >>= MV.putMVar future)
              return (Future future),
      pfun 1 "get" -: ""
                   -: "all '<a. '<a future -> '<a"
        -= (MV.takeMVar . unFuture),
      pfun 1 "coNew" -: ""
                     -: "all '<a. ('<a future -o unit) -> '<a cofuture"
        -= \f -> do
              future <- MV.newEmptyMVar
              CC.forkIO (vapp f (Future future) >> return ())
              return (Future future),
      pfun 1 "coPut" -: ""
                     -: "all '<a. '<a cofuture -> '<a -o unit"
        -= \future value -> MV.putMVar (unFuture future) value
    ],

    submod "SessionType" [
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
               else return (Right c)
    ],

    -- Unsafe coercions
    pfun 2 "unsafeCoerce" -:: "all '<b '<a. '<a -> '<b"
      -= (id :: Value -> Value),

    submod "IO"     Basis.IO.entries,

    submod "Thread" [
      -- Threads
      typeA "void",
      typeC "thread",
      fun "threadFork" -: "(unit -> unit) -> thread" -: ""
        -= \f -> Vinj `fmap` CC.forkIO (vapp f () >> return ()),
      fun "threadKill" -: "thread -> unit" -: ""
        -= CC.killThread . unVinj,
      fun "threadDelay" -:: "int -> unit"
        -= CC.threadDelay . (fromIntegral :: Integer -> Int),
      fun "printThread" -: "thread -> thread" -: ""
        -= \t -> do print (t :: Vinj CC.ThreadId); return t
    ],

    submod "Prim" [
      submod "Socket" Basis.Socket.entries
    ],

    submod "INTERNALS" [
      -- Used by contract system -- # names prevent them from appearing
      -- in a source program (which could result in nasty shadowing)
      pfun 1 "ref" -:: "all 'a. 'a -> 'a ref"
        -= (\v -> Ref `fmap` newIORef v),
      pfun 1 "modify" -:: "all 'a. 'a ref * 'a -> 'a"
        -= (\(vr, v1) -> do
              atomicModifyIORef (unRef vr) (\v0 -> (v1, v0))),
      fun "blame" -: "string -> string -> unit"
                  -: ""
        -= \who what -> fail $ "Contract violation: " ++
                               who ++ ": " ++
                               what :: IO (),

      submod "Exn" Basis.Exn.entries
    ]
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
  "open INTERNALS.Exn",
  "let[C] not (b: bool) = if b then false else true",
  "let[C] (!=)['a] (x: 'a) (y: 'a) = not (x == y)",
  "let[C] flip['a,'b,'c] (f: 'a -> 'b -> 'c) (y: 'b) (x: 'a) = f x y",
  "let[C] (<) (x: int) (y: int) = not (y <= x)",
  "let[C] (>) = flip (<)",
  "let[C] (>=) = flip (<=)",
  "let[C] (>.) = flip (<.)",
  "let[C] (>=.) = flip (<=.)",
  "let[C] null = fun 'a (x : 'a list) ->",
  "  match x with",
  "  | Nil -> true",
  "  | _   -> false",
  "let[C] hd = fun 'a (xs : 'a list) ->",
  "  let Cons(x, _) = xs in x",
  "let[C] tl = fun 'a (xs : 'a list) ->",
  "  let Cons(_, xs') = xs in xs'",
  "let[A] anull = fun '<a (xs : '<a list) ->",
  "  match xs with",
  "  | Nil          -> (Nil['<a], true)",
  "  | Cons(x, xs') -> (Cons(x, xs'), false)",
  "",
  "let[A] foldr =",
  "  let rec foldr '<a '<b (f : '<a -> '<b -o '<b)",
  "                        (z : '<b) |(xs : '<a list) : '<b =",
  "        match xs with",
  "        | Nil -> z",
  "        | Cons(x,xs) -> f x (foldr f z xs)",
  "   in foldr",
  "let[A] foldl =",
  "  let rec foldl '<a '<b (f : '<a -> '<b -o '<b)",
  "                        (z : '<b) |(xs : '<a list) : '<b =",
  "        match xs with",
  "        | Nil -> z",
  "        | Cons(x,xs) -> foldl f (f x z) xs",
  "   in foldl",
  "let[C] alist2clist : all 'a. {{'a} list} -> 'a list =",
  "  fun 'a (lst: {{'a} list}) ->",
  "    foldr (fun (x:'a) (xs:'a list) -> Cons(x, xs)) Nil['a] lst",
  "let[A] failwith (msg: string) =",
  "  raise (Failure msg)",
  ""
  ]
