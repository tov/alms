{-# LANGUAGE
      QuasiQuotes #-}
module Basis.Exn ( entries, ioexn2vexn ) where

import BasisUtils
import Value
import Quasi
import Syntax

import qualified Loc
import qualified Syntax.Notable

import Control.Exception

eiFailure, eiIOError, eiBlame, eiPatternMatch :: ExnId
eiFailure       = ExnId (-21) (Uid "Failure")
                    (Just [$ty| string |])
eiIOError       = ExnId (-22) (Uid "IOError")
                    (Just [$ty| string |])
eiBlame         = ExnId (-23) (Uid "Blame")
                    (Just [$ty| string * string|])
eiPatternMatch  = ExnId (-24) (Uid "PatternMatch")
                    (Just [$ty| string * string list|])

entries :: [Entry]
entries = [
    primexn eiFailure      $ Just [$ty| string |],
    primexn eiIOError      $ Just [$ty| string |],
    primexn eiBlame        $ Just [$ty| string * string |],
    primexn eiPatternMatch $ Just [$ty| string * string list |],

    fun "raise" -: [$ty| exn -> any |]
      -= \exn -> throw (vprj exn :: VExn)
                 :: IO Value,
    fun "tryfun" -: [$ty| all '<a. (unit -o '<a) -> exn + '<a |]
      -= \(VaFun _ f) -> try (ioexn2vexn (f vaUnit))
                         :: IO (Either VExn Value),

    fun "raiseBlame" -: [$ty| string -> string -> any |]
      -= \s1 s2 -> throw VExn {
           exnId    = eiBlame,
           exnParam = Just (vinj (s1 :: String, s2 :: String))
         } :: IO Value
  ]

ioexn2vexn :: IO a -> IO a
ioexn2vexn  = handle $ \e ->
  throw VExn {
    exnId    = eiIOError,
    exnParam = Just (vinj (show (e :: IOException)))
  }
