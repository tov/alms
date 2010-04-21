module Basis.Exn ( entries, ioexn2vexn ) where

import BasisUtils
import Value
import Syntax (ExnId(..), eiIOError, eiBlame, eiPatternMatch)

import Control.Exception

-- raiseExn :: Valueable v => String -> Maybe v

entries :: [Entry]
entries = [
    primexn eiIOError      "string",
    primexn eiBlame        "string * string",
    primexn eiPatternMatch "string * string list",
    src "exception Failure of string",

    pfun 1 "raise" -: "exn -> any"
      -= \exn -> throw (vprj exn :: VExn)
                 :: IO Value,
    pfun 1 "try" -: "all '<a. (unit -o '<a) -> exn + '<a"
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
