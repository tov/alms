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
import Data.IORef (IORef, newIORef, atomicModifyIORef)
import Data.Typeable

-- For references (and printing them)
newtype Ref = Ref { unRef :: IORef Value }
  deriving (Eq, Typeable)

instance Valuable Ref where
  veq = (==)
  vpprPrec _ _ = text "#<ref>"

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

    fun "#blame" -: "string -> string -> unit"
                 -: ""
      -= \who what -> fail $ "Contract violation: " ++
                             who ++ ": " ++
                             what :: IO (),

    fun "putStr"   -:: "string -> unit"
      -= putStr,
    fun "putStrLn" -:: "string -> unit"
      -= putStrLn,
    fun "getLine"  -:: "unit -> string"
      -= \() -> getLine,
    fun "explode"  -:: "string -> int list"
      -= map (vinj . char2integer),
    fun "implode"  -:: "int list -> string"
      -= vinj . map (integer2char . vprj)
  ]

