{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE
      DeriveDataTypeable,
      StandaloneDeriving
  #-}
module Basis.IO ( entries ) where

import qualified IO

import Data.Typeable (Typeable)
import BasisUtils
import Value (Valuable(..), vinjEnum, vprjEnum)
import Ppr (text)
import Util

instance Valuable IO.Handle where
  veq = (==)
  vpprPrec _ _ = text "#<handle>"

instance Valuable IO.IOMode where
  veq      = (==)
  vpprPrec _ = text . show
  vinj     = vinjEnum
  vprjM    = vprjEnum
deriving instance Typeable IO.IOMode

entries :: [Entry]
entries = [
    -- File operations
    typeC "handle",
    typeC "ioMode = ReadMode | WriteMode | AppendMode | ReadWriteMode",
    fun "openFile"        -: "string -> ioMode -> handle" -: ""
      -= IO.openFile,
    fun "hGetChar"        -: "handle -> char" -: ""
      -= fmap char2integer . IO.hGetChar,
    fun "hGetLine"        -: "handle -> string" -: ""
      -= IO.hGetLine,
    fun "hIsEOF"          -: "handle -> bool" -: ""
      -= IO.hIsEOF,
    fun "hPutChar"        -: "handle -> char -> unit" -: ""
      -= \h -> IO.hPutChar h . integer2char,
    fun "hPutStr"         -: "handle -> string -> unit" -: ""
      -= IO.hPutStr,
    fun "hClose"          -: "handle -> unit" -: ""
      -= IO.hClose,
    fun "hFlush"          -: "handle -> unit" -: ""
      -= IO.hFlush,

    val "stdin"  -: "handle" -: "" -= IO.stdin,
    val "stdout" -: "handle" -: "" -= IO.stdout,
    val "stderr" -: "handle" -: "" -= IO.stderr
  ]
