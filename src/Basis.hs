-- | Built-in operations and types
{-# LANGUAGE
      DeriveDataTypeable,
      QuasiQuotes,
      TemplateHaskell #-}
module Basis (
  primBasis, srcBasis, basis2venv, basis2tenv
) where

import Util
import BasisUtils
import Value (Valuable(..), Value(..))
import Syntax
import Type

import qualified Syntax.Notable
import qualified Syntax.Decl
import qualified Data.Loc

import qualified Basis.IO
import qualified Basis.Socket
import qualified Basis.Exn
import qualified Basis.Thread
import qualified Basis.Channel
import qualified Basis.MVar
import qualified Basis.Future
import qualified Basis.Array

import qualified IO
import qualified System.Environment as Env
import Data.IORef (IORef, newIORef, readIORef, atomicModifyIORef)
import System.Random (randomIO)
import Data.Typeable

-- Primitive operations implemented in Haskell
primBasis :: [Entry Raw]
primBasis  = [
    ---
    --- Ordinary constants:
    ---

    --- name    -: type -= value

    -- Primitive types:
    "unit"   `primtype` tcUnit,
    "any"    `primtype` tcBot,
    "exn"    `primtype` tcExn,
    dec [$dc| type bool = false | true |],
    "int"    `primtype` tcInt,
    dec [$dc| type char = int |],
    "float"  `primtype` tcFloat,
    "string" `primtype` tcString,
    "U"      `primtype` tcUn,
    "A"      `primtype` tcAf,
    "*"      `primtype` tcTuple,

    -- Sums
    dec [$dc| type `a option = None | Some of `a |],
    dec [$dc| type `a + `b = Left of `a | Right of `b |],

    -- Lists
    dec [$dc| type `a list = Nil | Cons of `a * `a list |],

    -- Arithmetic
    binArith "+" (+),
    binArith "-" (-),
    binArith "*" (*),
    binArith "/" div,
    binArith "%" mod,
    fun "~" -: [$ty| int -> int |]
      -= (negate :: Integer -> Integer),
    fun "abs" -: [$ty| int -> int |]
      -= (abs :: Integer -> Integer) ,
    fun "<=" -: [$ty| int -> int -> bool |]
      -= ((<=) :: Integer -> Integer -> Bool),
    fun "string_of_int" -: [$ty| int -> string |]
      -= (show :: Integer -> String),
    fun "int_of_string" -: [$ty| string -> int |]
      -= (read :: String -> Integer),
    fun "random_int" -: [$ty| unit -> int |]
      -= \() -> (randomIO :: IO Int),

    -- Floating point arithmetic
    fun "<=." -: [$ty| float -> float -> bool |]
      -= ((<=) :: Double -> Double -> Bool),
    fun "<." -: [$ty| float -> float -> bool |]
      -= ((<) :: Double -> Double -> Bool),
    fun "+." -: [$ty| float -> float -> float |]
      -= ((+) :: Double -> Double -> Double),
    fun "-." -: [$ty| float -> float -> float |]
      -= ((-) :: Double -> Double -> Double),
    fun "*." -: [$ty| float -> float -> float |]
      -= ((*) :: Double -> Double -> Double),
    fun "/." -: [$ty| float -> float -> float |]
      -= ((/) :: Double -> Double -> Double),
    fun "**" -: [$ty| float -> float -> float |]
      -= ((**) :: Double -> Double -> Double),
    fun "~." -: [$ty| float -> float |]
      -= (negate :: Double -> Double),
    fun "sqrt" -: [$ty| float -> float |]
      -= (sqrt :: Double -> Double),
    fun "log" -: [$ty| float -> float |]
      -= (log :: Double -> Double),
    fun "absf" -: [$ty| float -> float |]
      -= (abs :: Double -> Double),
    fun "float_of_int" -: [$ty| int -> float |]
      -= (fromIntegral :: Integer -> Double),
    fun "int_of_float" -: [$ty| float -> int |]
      -= (round :: Double -> Integer),
    fun "string_of_float" -: [$ty| float -> string |]
      -= (show :: Double -> String),
    fun "float_of_string" -: [$ty| string -> float |]
      -= (read :: String -> Double),

    -- Strings
    fun "explode"  -: [$ty| string -> char list |]
      -= map char2integer,
    fun "implode"  -: [$ty| char list -> string |]
      -= map integer2char,
    fun "^" -: [$ty| string -> string -> string |]
      -= ((++) :: String -> String -> String),
    fun "string_of" -: [$ty| all 'a. 'a -> string |]
      -= (return . show :: Value -> IO String),
    fun "string_length" -: [$ty| string -> int |]
      -= \s -> toInteger (length (s :: String)),

    -- "Magic" equality and print; failure
    fun "==" -: [$ty| all 'a. 'a -> 'a -> bool |]
      -= ((==) :: Value -> Value -> Bool),
    fun "print" -: [$ty| all 'a. 'a -> unit |]
      -= (print :: Value -> IO ()),

    -- I/O
    fun "putChar"  -: [$ty| char -> unit |]
      -= putChar . integer2char,
    fun "getChar"  -: [$ty| unit -> char |]
      -= \() -> fmap char2integer getChar,
    fun "flush"    -: [$ty| unit -> unit |]
      -= \() -> IO.hFlush IO.stdout,
    fun "putStr"   -: [$ty| string -> unit |]
      -= putStr,
    fun "putStrLn" -: [$ty| string -> unit |]
      -= putStrLn,
    fun "getLine"  -: [$ty| unit -> string |]
      -= \() -> getLine,

    -- The environment
    fun "getArgs" -: [$ty| unit -> string list |]
      -= \() -> Env.getArgs,
    fun "getProgName" -: [$ty| unit -> string |]
      -= \() -> Env.getProgName,
    fun "getEnv" -: [$ty| string -> string |]
      -= Env.getEnv,
    fun "getEnvironment" -: [$ty| unit -> (string * string) list |]
      -= \() -> Env.getEnvironment,

    -- References
    dec [$dc| type `a ref qualifier U |],
    dec [$dc| type `a aref qualifier A |],
    fun "ref" -: [$ty| all `a. `a -> `a ref |]
      -= (\v -> Ref `fmap` newIORef v),
    fun "aref" -: [$ty| all `a. `a -> `a aref |]
      -= (\v -> Ref `fmap` newIORef v),

    fun "!" -: [$ty| all 'a. 'a ref -> 'a |]
      -= (\r -> readIORef (unRef r)),
    fun "!!" -: [$ty| all 'a. 'a aref -> 'a aref * 'a |]
      -= (\r -> do
           v <- readIORef (unRef r)
           return (r, v)),
    fun "<-" -: [$ty| all `a. `a ref -> `a -> `a |]
      -= (\r v -> do
           atomicModifyIORef (unRef r) (\v' -> (v, v'))),
    fun "<-!" -: [$ty| all `a `b. `a aref ->
                            `b -o `b aref * `a |]
      -= (\r v -> do
           atomicModifyIORef (unRef r) (\v' -> (v, (r, v')))),

    submod "Unsafe" [
      -- Unsafe coercions
      fun "unsafeCoerce" -: [$ty| all `b `a. `a -> `b |]
        -= (id :: Value -> Value),
      fun "unsafeDup" -: [$ty| all `a. `a -> `a * `a |]
        -= ((\v -> (v, v)) :: Value -> (Value, Value))
    ],

    submod "IO"      Basis.IO.entries,
    submod "Channel" Basis.Channel.entries,
    submod "Thread"  Basis.Thread.entries,
    submod "MVar"    Basis.MVar.entries,
    submod "Future"  Basis.Future.entries,

    submod "Prim" [
      submod "Socket" Basis.Socket.entries,
      submod "Exn"    Basis.Exn.entries,
      submod "Array"  Basis.Array.entries
    ]
  ]

newtype Ref = Ref { unRef :: IORef Value }
  deriving (Eq, Typeable)

instance Valuable Ref where
  veq = (==)
  vppr _ = text "#<ref>"

-- | Built-in operations implemented in the object language
srcBasis :: String
srcBasis  = "libbasis.alms"
