module Basis.Exn ( entries, ioexn2vexn ) where

import BasisUtils
import Value
import Syntax (Type, tyNulOp, tyTuple)

import Control.Exception

tyString :: Type ()
tyString  = tyNulOp "string"

eiFailure, eiIOError, eiBlame, eiPatternMatch :: ExnId
eiFailure       = ExnId (-21) (Uid "Failure")
                    (Just tyString)
eiIOError       = ExnId (-22) (Uid "IOError")
                    (Just tyString)
eiBlame         = ExnId (-23) (Uid "Blame")
                    (Just (tyString `tyTuple` tyString))
eiPatternMatch  = ExnId (-24) (Uid "PatternMatch")
                    (Just (tyString `tyTuple` tyString `tyTuple` tyString))

entries :: [Entry]
entries = [
    primexn eiFailure      "string",
    primexn eiIOError      "string",
    primexn eiBlame        "string * string",
    primexn eiPatternMatch "string * string list",

    pfun 1 "raise" -: "exn -> any"
      -= \exn -> throw (vprj exn :: VExn)
                 :: IO Value,
    pfun 1 "tryfun" -: "all '<a. (unit -o '<a) -> exn + '<a"
      -= \(VaFun _ f) -> try (ioexn2vexn (f vaUnit))
                         :: IO (Either VExn Value),

    fun "raiseBlame" -: "string -> string -> any"
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
