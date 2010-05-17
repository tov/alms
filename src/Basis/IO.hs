{-# LANGUAGE
      DeriveDataTypeable,
      QuasiQuotes,
      StandaloneDeriving
  #-}
module Basis.IO ( entries ) where

import qualified IO

import Data.Data (Typeable, Data)
import BasisUtils
import Syntax
import Util
import Value (Valuable(..), vinjData, vprjDataM)

import qualified Loc
import qualified Syntax.Notable
import qualified Syntax.Decl

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
    dec [$dc|+ type handle |],
    dec [$dc|+ type ioMode = ReadMode
                           | WriteMode
                           | AppendMode
                           | ReadWriteMode |],
    -- File operations
    fun "openFile"        -: [$ty|+ string -> ioMode -> handle |]
      -= IO.openFile,
    fun "hGetChar"        -: [$ty|+ handle -> char |]
      -= fmap char2integer . IO.hGetChar,
    fun "hGetLine"        -: [$ty|+ handle -> string |]
      -= IO.hGetLine,
    fun "hIsEOF"          -: [$ty|+ handle -> bool |]
      -= IO.hIsEOF,
    fun "hPutChar"        -: [$ty|+ handle -> char -> unit |]
      -= \h -> IO.hPutChar h . integer2char,
    fun "hPutStr"         -: [$ty|+ handle -> string -> unit |]
      -= IO.hPutStr,
    fun "hClose"          -: [$ty|+ handle -> unit |]
      -= IO.hClose,
    fun "hFlush"          -: [$ty|+ handle -> unit |]
      -= IO.hFlush,

    val "stdin"  -: [$ty|+ handle |] -= IO.stdin,
    val "stdout" -: [$ty|+ handle |] -= IO.stdout,
    val "stderr" -: [$ty|+ handle |] -= IO.stderr
  ]
