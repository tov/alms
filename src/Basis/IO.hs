{-# LANGUAGE
      DeriveDataTypeable,
      StandaloneDeriving
  #-}
module Basis.IO ( entries ) where

import qualified IO

import Data.Data (Typeable, Data)
import BasisUtils
import Value (Valuable(..), vinjData, vprjDataM)
import Util

instance Valuable IO.Handle where
  veq = (==)
  vpprPrec _ _ = text "#<handle>"

instance Valuable IO.IOMode where
  veq      = (==)
  vpprPrec _ = text . show
  vinj     = vinjData
  vprjM    = vprjDataM
deriving instance Typeable IO.IOMode
deriving instance Data IO.IOMode

entries :: [Entry]
entries = [
    typ "handle",
    typ "ioMode = ReadMode | WriteMode | AppendMode | ReadWriteMode",
    -- File operations
    fun "openFile"        -: "string -> ioMode -> handle"
      -= IO.openFile,
    fun "hGetChar"        -: "handle -> char"
      -= fmap char2integer . IO.hGetChar,
    fun "hGetLine"        -: "handle -> string"
      -= IO.hGetLine,
    fun "hIsEOF"          -: "handle -> bool"
      -= IO.hIsEOF,
    fun "hPutChar"        -: "handle -> char -> unit"
      -= \h -> IO.hPutChar h . integer2char,
    fun "hPutStr"         -: "handle -> string -> unit"
      -= IO.hPutStr,
    fun "hClose"          -: "handle -> unit"
      -= IO.hClose,
    fun "hFlush"          -: "handle -> unit"
      -= IO.hFlush,

    val "stdin"  -: "handle" -= IO.stdin,
    val "stdout" -: "handle" -= IO.stdout,
    val "stderr" -: "handle" -= IO.stderr
  ]
