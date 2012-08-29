module Basis.IO ( entries ) where

import qualified Data.Loc
import BasisUtils
import AST
import Util
import Value (Valuable(..), vinjData, vprjDataM)

import qualified System.IO as IO
import Data.Data (Typeable, Data)

instance Valuable IO.Handle where
  veq = (==)
  vppr _ = text "#<handle>"

instance Valuable IO.IOMode where
  veq      = (==)
  vppr     = text . show
  vinj     = vinjData
  vprjM    = vprjDataM
deriving instance Typeable IO.IOMode
deriving instance Data IO.IOMode

entries :: [Entry Raw]
entries = [
    dec [sgQ| type handle |],
    dec [sgQ| type ioMode = ReadMode
                           | WriteMode
                           | AppendMode
                           | ReadWriteMode |],
    -- File operations
    fun "openFile"        -: [ty| string -> ioMode -> handle |]
      -= IO.openFile,
    fun "hGetChar"        -: [ty| handle -> char |]
      -= fmap char2integer . IO.hGetChar,
    fun "hGetLine"        -: [ty| handle -> string |]
      -= IO.hGetLine,
    fun "hIsEOF"          -: [ty| handle -> bool |]
      -= IO.hIsEOF,
    fun "hPutChar"        -: [ty| handle -> char -> unit |]
      -= \h -> IO.hPutChar h . integer2char,
    fun "hPutStr"         -: [ty| handle -> string -> unit |]
      -= IO.hPutStr,
    fun "hClose"          -: [ty| handle -> unit |]
      -= IO.hClose,
    fun "hFlush"          -: [ty| handle -> unit |]
      -= IO.hFlush,

    val "stdin"  -: [ty| handle |] -= IO.stdin,
    val "stdout" -: [ty| handle |] -= IO.stdout,
    val "stderr" -: [ty| handle |] -= IO.stderr
  ]
