{-# LANGUAGE
      QuasiQuotes #-}
module Basis.Exn ( entries ) where

import BasisUtils
import Value
import Syntax
import Util

import qualified Loc
import qualified Syntax.Notable

import Control.Exception

eiFailure, eiIOError, eiBlame, eiPatternMatch :: ExnId Raw
eiFailure       = ExnId (-21) (uid "Failure")
                    (Just [$ty| string |])
eiIOError       = ExnId (-22) (uid "IOError")
                    (Just [$ty| string |])
eiBlame         = ExnId (-23) (uid "Blame")
                    (Just [$ty| string * string|])
eiPatternMatch  = ExnId (-24) (uid "PatternMatch")
                    (Just [$ty| string * string list|])

entries :: [Entry Raw]
entries = [
    primexn eiFailure,
    primexn eiIOError,
    primexn eiBlame,
    primexn eiPatternMatch,

    fun "raise" -: [$ty| exn -> any |]
      -= \exn -> throw (vprj exn :: VExn)
                 :: IO Value,
    fun "tryfun_string"
                -: [$ty| all '<a. (unit -o '<a) -> string + (exn + '<a) |]
      -= \(VaFun _ f) -> left show `fmap`
                          (try
                           (try (f vaUnit) :: IO (Either VExn Value))
                           :: IO (Either IOError (Either VExn Value)))
                 :: IO (Either String (Either VExn Value))
  ]
