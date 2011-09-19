module Basis.Channel (Channel, entries) where

import Data.Typeable (Typeable)
import BasisUtils
import AST
import Value (Value, Valuable(..))

import qualified Data.Loc

import qualified Basis.Channel.Haskell as C

newtype Channel = Channel { unChannel :: C.Chan Value }
  deriving (Eq, Typeable)

instance Valuable Channel where
  veq = (==)
  vppr _ = text "#<channel>"

entries :: [Entry Raw]
entries  = [
    dec [sgQ| type `a channel |],
    fun "new"  -: [ty| all `a. unit -> `a channel |]
        -= \() -> Channel `fmap` C.newChan,
    fun "send" -: [ty| all `a. `a channel -> `a -> unit |]
        -= \c a -> do
             C.writeChan (unChannel c) a
             return (),
    fun "recv" -: [ty| all `a. `a channel -> `a |]
        -= \c -> C.readChan (unChannel c)
  ]
