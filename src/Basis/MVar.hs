{-# LANGUAGE
      DeriveDataTypeable,
      QuasiQuotes #-}
module Basis.MVar (entries) where

import Data.Typeable (Typeable)
import BasisUtils
import Quasi
import Syntax
import Util
import Value (Value, Valuable(..))

import qualified Control.Concurrent.MVar as MV

newtype MVar = MVar { unMVar :: MV.MVar Value }
  deriving (Eq, Typeable)

instance Valuable MVar where
  veq = (==)
  vpprPrec _ _ = text "#<mvar>"

entries :: [Entry]
entries  = [
    dec [$dc| type '<a mvar qualifier U |],
    fun "new" -: [$ty| all '<a. '<a -> '<a mvar |]
      -= liftM MVar . MV.newMVar,
    fun "newEmpty"
                 -: [$ty| all '<a. unit -> '<a mvar |]
      -= \() -> MVar `liftM` MV.newEmptyMVar,
    fun "take"
                 -: [$ty| all '<a. '<a mvar -> '<a |]
      -= MV.takeMVar . unMVar,
    fun "put"
                 -: [$ty| all '<a. '<a mvar -> '<a -> unit |]
      -= MV.putMVar . unMVar,
    fun "read"
                 -: [$ty| all 'a. 'a mvar -> 'a |] -- important!
      -= MV.readMVar . unMVar,
    fun "swap"
                 -: [$ty| all '<a. '<a mvar -> '<a -> '<a |]
      -= MV.swapMVar . unMVar,
    fun "tryTake"
                 -: [$ty| all '<a. '<a mvar -> '<a option |]
      -= MV.tryTakeMVar . unMVar,
    fun "tryPut"
                 -: [$ty| all '<a. '<a mvar -> '<a -> bool |]
      -= MV.tryPutMVar . unMVar,
    fun "isEmpty"
                 -: [$ty| all '<a. '<a mvar -> bool |]
      -= MV.isEmptyMVar . unMVar,
    fun "callWith"
                 -: [$ty| all '<a '<b. '<a mvar -> ('<a -> '<b) -> '<b |]
      -= \mv callback -> MV.withMVar (unMVar mv) (vapp callback),
    fun "modify_"
                 -: [$ty| all '<a. '<a mvar -> ('<a -> '<a) -> unit |]
      -= \mv callback -> MV.modifyMVar_ (unMVar mv) (vapp callback),
    fun "modify"
                 -: [$ty| all '<a '<b. '<a mvar -> ('<a -> '<a * '<b) -> '<b |]
      -= \mv callback -> MV.modifyMVar (unMVar mv) $ \v -> do
                           result <- vapp callback v
                           (vprjM result :: IO (Value, Value))
  ]

