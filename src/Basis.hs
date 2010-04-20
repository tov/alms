-- | Built-in operations and types
{-#
  LANGUAGE DeriveDataTypeable
  #-}
module Basis (
  primBasis, srcBasis, basis2venv, basis2tenv
) where

import Util
import BasisUtils
import Value (Valuable(..), Value(..))
import Ppr (text)
import Syntax

import qualified Basis.IO
import qualified Basis.Socket
import qualified Basis.Exn
import qualified Basis.Thread
import qualified Basis.Channel
import qualified Basis.MVar
import qualified Basis.Future

import qualified IO
import qualified System.Environment as Env
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef)
import Data.Typeable
import Control.Monad
import Control.Monad.Fix

-- Primitive operations implemented in Haskell
primBasis :: [Entry]
primBasis  = [
    ---
    --- Ordinary constants:
    ---

    --- name    -:  ctype  -: atype  -= value
    --- name    -: *type            -= value

    -- Primitive types:
    -- "unit" built in
    typ "any  = all '<a. '<a",
    typ "bool = false | true",
    "int"    `primtype` tdInt,
    typ "char = int",
    "float"  `primtype` tdFloat,
    "string" `primtype` tdString,

    "*"    `primtype` tdTuple,
    "->"   `primtype` tdArr,
    "-o"   `primtype` tdLol,

    -- Sums
    typ "'<a option = None | Some of '<a",
    typ "'<a + '<b = Left of '<a | Right of '<b",

    -- Recursion
    pfun 2 "fix" -: "all 'a 'b. (('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b)"
      -= (\(VaFun _ f) -> mfix f),

    -- Lists
    typ "'<a list = Nil | Cons of '<a * '<a list",

    -- Arithmetic
    binArith "+" (+),
    binArith "-" (-),
    binArith "*" (*),
    binArith "/" div,
    binArith "%" mod,
    fun "~" -: "int -> int"
      -= (negate :: Integer -> Integer),
    fun "abs" -: "int -> int"
      -= (abs :: Integer -> Integer),
    fun "<=" -: "int -> int -> bool"
      -= ((<=) :: Integer -> Integer -> Bool),

    -- Floating point arithmetic
    fun "<=." -: "float -> float -> bool"
      -= ((<=) :: Double -> Double -> Bool),
    fun "<." -: "float -> float -> bool"
      -= ((<) :: Double -> Double -> Bool),
    fun "+." -: "float -> float -> float"
      -= ((+) :: Double -> Double -> Double),
    fun "-." -: "float -> float -> float"
      -= ((-) :: Double -> Double -> Double),
    fun "*." -: "float -> float -> float"
      -= ((*) :: Double -> Double -> Double),
    fun "/." -: "float -> float -> float"
      -= ((/) :: Double -> Double -> Double),
    fun "**" -: "float -> float -> float"
      -= ((**) :: Double -> Double -> Double),
    fun "~." -: "float -> float"
      -= (negate :: Double -> Double),
    fun "sqrt" -: "float -> float"
      -= (sqrt :: Double -> Double),
    fun "log" -: "float -> float"
      -= (log :: Double -> Double),
    fun "absf" -: "float -> float"
      -= (abs :: Double -> Double),
    fun "float_of_int" -: "int -> float"
      -= (fromIntegral :: Integer -> Double),
    fun "int_of_float" -: "float -> int"
      -= (round :: Double -> Integer),
    fun "string_of_float" -: "float -> string"
      -= (show :: Double -> String),
    fun "float_of_string" -: "string -> float"
      -= (read :: String -> Double),
    fun "string_of_int" -: "int -> string"
      -= (show :: Integer -> String),
    fun "int_of_string" -: "string -> int"
      -= (read :: String -> Integer),

    -- Strings
    fun "explode"  -: "string -> int list"
      -= map char2integer,
    fun "implode"  -: "int list -> string"
      -= map integer2char,
    fun "^" -: "string -> string -> string"
      -= ((++) :: String -> String -> String),
    pfun 1 "string_of" -: "all 'a. 'a -> string"
      -= (return . show :: Value -> IO String),
    fun "string_length" -: "string -> int"
      -= \s -> toInteger (length (s :: String)),

    -- "Magic" equality and print; failure
    pfun 1 "==" -: "all 'a. 'a -> 'a -> bool"
      -= ((==) :: Value -> Value -> Bool),
    pfun 1 "print" -: "all 'a. 'a -> unit"
      -= (print :: Value -> IO ()),

    -- I/O
    fun "putChar"  -: "int -> unit"
      -= putChar . integer2char,
    fun "getChar"  -: "unit -> int"
      -= \() -> fmap char2integer getChar,
    fun "flush"    -: "unit -> unit"
      -= \() -> IO.hFlush IO.stdout,
    fun "putStr"   -: "string -> unit"
      -= putStr,
    fun "putStrLn" -: "string -> unit"
      -= putStrLn,
    fun "getLine"  -: "unit -> string"
      -= \() -> getLine,

    -- The environment
    fun "getArgs" -: "unit -> string list"
      -= \() -> Env.getArgs,
    fun "getProgName" -: "unit -> string"
      -= \() -> Env.getProgName,
    fun "getEnv" -: "string -> string"
      -= Env.getEnv,
    fun "getEnvironment" -: "unit -> (string * string) list"
      -= \() -> Env.getEnvironment,

    -- References
    typ "'<a ref qualifier U",
    typ "'<a aref qualifier A",
    pfun 1 "ref" -: "all '<a. '<a -> '<a ref"
      -= (\v -> Ref `fmap` newIORef v),
    pfun 1 "aref" -: "all '<a. '<a -> '<a aref"
      -= (\v -> Ref `fmap` newIORef v),

    pfun 1 "!" -: "all 'a. 'a ref -> 'a"
      -= (\r -> readIORef (unRef r)),
    pfun 1 "!!" -: "all 'a. 'a aref -> 'a aref * 'a"
      -= (\r -> do
           v <- readIORef (unRef r)
           return (r, v)),
    pfun 1 "<-" -: "all '<a. '<a ref -> '<a -o '<a"
      -= (\r v -> do
           atomicModifyIORef (unRef r) (\v' -> (v, v'))),
    pfun 1 "<-!" -: "all '<a '<b. '<a aref -> '<b -o '<b aref * '<a"
      -= (\r v -> do
           atomicModifyIORef (unRef r) (\v' -> (v, (r, v')))),

    submod "Unsafe" [
      -- Unsafe coercions
      pfun 2 "unsafeCoerce" -: "all '<b '<a. '<a -> '<b"
        -= (id :: Value -> Value),
      pfun 1 "unsafeDup" -: "all '<a. '<a -> '<a * '<a"
        -= ((\v -> (v, v)) :: Value -> (Value, Value))
    ],

    submod "IO"      Basis.IO.entries,
    submod "Channel" Basis.Channel.entries,
    submod "Thread"  Basis.Thread.entries,
    submod "MVar"    Basis.MVar.entries,
    submod "Future"  Basis.Future.entries,

    submod "Prim" [
      submod "Socket" Basis.Socket.entries,
      submod "SessionType" [
        "dual"   `primtype` tdDual,
        "send"   `primtype` tdSend,
        "recv"   `primtype` tdRecv,
        "select" `primtype` tdSelect,
        "follow" `primtype` tdFollow
      ]
    ],

    submod "INTERNALS" [
      -- Used by contract system -- # names prevent them from appearing
      -- in a source program (which could result in nasty shadowing)
      pfun 1 "ref" -: "all 'a. 'a -> 'a ref"
        -= (\v -> Ref `fmap` newIORef v),
      pfun 1 "modify" -: "all 'a. 'a ref * 'a -> 'a"
        -= (\(vr, v1) -> do
              atomicModifyIORef (unRef vr) (\v0 -> (v1, v0))),
      fun "blame" -: "string -> string -> unit"
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

-- | Built-in operations implemented in the object language
srcBasis :: String
srcBasis  = unlines [
  "open INTERNALS.Exn",
  "let not (b: bool) = if b then false else true",
  "let (!=)['a] (x: 'a) (y: 'a) = not (x == y)",
  "let flip['a,'b,'c] (f: 'a -> 'b -> 'c) (y: 'b) (x: 'a) = f x y",
  "let (<) (x: int) (y: int) = not (y <= x)",
  "let (>) = flip (<)",
  "let (>=) = flip (<=)",
  "let (>.) = flip (<.)",
  "let (>=.) = flip (<=.)",
  "let null = fun 'a (x : 'a list) ->",
  "  match x with",
  "  | Nil -> true",
  "  | _   -> false",
  "let hd = fun 'a (xs : 'a list) ->",
  "  let Cons(x, _) = xs in x",
  "let tl = fun 'a (xs : 'a list) ->",
  "  let Cons(_, xs') = xs in xs'",
  "let fst['<a,'<b] (x: '<a, _: '<b) = x",
  "let snd['<a,'<b] (_: '<a, y: '<b) = y",
  "let (=>!) ['<a] (x: '<a) ['<b] (y: '<b) = (y, x)",
  "let anull = fun '<a (xs : '<a list) ->",
  "  match xs with",
  "  | Nil          -> (Nil['<a], true)",
  "  | Cons(x, xs') -> (Cons(x, xs'), false)",
  "",
  "let foldr =",
  "  let rec foldr '<a '<b (f : '<a -> '<b -o '<b)",
  "                        (z : '<b) |(xs : '<a list) : '<b =",
  "        match xs with",
  "        | Nil -> z",
  "        | Cons(x,xs) -> f x (foldr f z xs)",
  "   in foldr",
  "let foldl =",
  "  let rec foldl '<a '<b (f : '<a -> '<b -o '<b)",
  "                        (z : '<b) |(xs : '<a list) : '<b =",
  "        match xs with",
  "        | Nil -> z",
  "        | Cons(x,xs) -> foldl f (f x z) xs",
  "   in foldl",
  "let revApp['<a] (xs : '<a list) (ys : '<a list) =",
  "  let cons (x : '<a) (acc : '<a list) = Cons (x, acc) in",
  "    foldl cons ys xs",
  "let rev['<a] (xs : '<a list) = revApp xs Nil",
  "let append['<a] (xs : '<a list) = revApp (rev xs)",
  "let length['<a] (xs : '<a list) =",
  "  foldr (fun (x : '<a) -> (+) 1) 0 xs",
  "let lengthA['<a] (xs : '<a list) =",
  "  let count (x : '<a) (xs' : '<a list, n : int) =",
  "       (Cons (x, xs'), 1 + n) in",
  "    foldr count (Nil['<a], 0) xs",
  "let failwith (msg: string) =",
  "  raise (Failure msg)",
  ""
  ]
