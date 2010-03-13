{-# LANGUAGE DeriveDataTypeable #-}
module Basis.Channel (Channel, entries) where

import Data.Typeable (Typeable)
import BasisUtils
import Value (Value, Valuable(..))
import Ppr (text)
import Util

import qualified Basis.Channel.Haskell as C

newtype Channel = Channel { unChannel :: C.Chan Value }
  deriving (Eq, Typeable)

instance Valuable Channel where
  veq = (==)
  vpprPrec _ _ = text "#<channel>"

entries :: [Entry]
entries  = [
    typeC "'a channel",
    pfun 1 "new"  -: "all 'a. unit -> 'a channel"
                  -: ""
        -= \() -> Channel `fmap` C.newChan,
    pfun 2 "send" -: "all 'a. 'a channel -> 'a -> unit"
                  -: ""
        -= \c a -> do
             C.writeChan (unChannel c) a
             return (),
    pfun 1 "recv" -: "all 'a. 'a channel -> 'a"
                  -: ""
        -= \c -> C.readChan (unChannel c)
  ]
