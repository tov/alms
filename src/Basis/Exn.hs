module Basis.Exn ( entries, ioexn2vexn ) where

import BasisUtils
import Value
import Syntax (LangRepMono(..), exidIOError, exidBlame)

import Control.Exception

entries :: [Entry]
entries = [
    exnC "IOError" exidIOError "string",
    exnC "Blame"   exidBlame   "string * string",
    src "exception[C] Failure of string",

    pfun 1 "raise" -:: "all '<a. exn -> '<a"
      -= \exn -> throw (vprj exn :: VExn)
                 :: IO Value,
    pfun 1 "tryC" -: "all 'a. (unit -> 'a) -> (exn, 'a) either"
                  -: "all '<a. (unit -o '<a) -> (exn, '<a) either"
      -= \(VaFun _ f) ->
           tryJust (\e -> if exnLang e == LC then Just e else Nothing)
                   (ioexn2vexn (f vaUnit)),
    pfun 1 "tryA" -: ""
                  -: "all '<a. (unit -o '<a) -> (exn, '<a) either"
      -= \(VaFun _ f) -> try (ioexn2vexn (f vaUnit))
                         :: IO (Either VExn Value),

    fun "liftExn" -: ""
                  -: "{exn} -> exn"
      -= (id :: Value -> Value),

    fun "raiseBlame" -:: "string -> string -> unit"
      -= \s1 s2 -> throw VExn {
           exnName  = Uid "Blame",
           exnParam = Just (vinj (s1 :: String, s2 :: String)),
           exnIndex = exidBlame,
           exnLang  = LC
         } :: IO Value
  ]

ioexn2vexn :: IO a -> IO a
ioexn2vexn  = handle $ \e ->
  throw VExn {
    exnName  = Uid "IOError",
    exnParam = Just (vinj (show (e :: IOException))),
    exnIndex = exidIOError,
    exnLang  = LC
  }
