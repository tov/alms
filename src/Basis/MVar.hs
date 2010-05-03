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
    pfun 1 "new" -: [$ty| all '<a. '<a -> '<a mvar |]
      -= liftM MVar . MV.newMVar,
    pfun 1 "newEmpty"
                 -: [$ty| all '<a. unit -> '<a mvar |]
      -= \() -> MVar `liftM` MV.newEmptyMVar,
    pfun 1 "take"
                 -: [$ty| all '<a. '<a mvar -> '<a |]
      -= MV.takeMVar . unMVar,
    pfun 1 "put"
                 -: [$ty| all '<a. '<a mvar -> '<a -> unit |]
      -= MV.putMVar . unMVar,
    pfun 1 "read"
                 -: [$ty| all 'a. 'a mvar -> 'a |] -- important!
      -= MV.readMVar . unMVar,
    pfun 1 "swap"
                 -: [$ty| all '<a. '<a mvar -> '<a -> '<a |]
      -= MV.swapMVar . unMVar,
    pfun 1 "tryTake"
                 -: [$ty| all '<a. '<a mvar -> '<a option |]
      -= MV.tryTakeMVar . unMVar,
    pfun 1 "tryPut"
                 -: [$ty| all '<a. '<a mvar -> '<a -> bool |]
      -= MV.tryPutMVar . unMVar,
    pfun 1 "isEmpty"
                 -: [$ty| all '<a. '<a mvar -> bool |]
      -= MV.isEmptyMVar . unMVar,
    pfun 1 "callWith"
                 -: [$ty| all '<a '<b. '<a mvar -> ('<a -> '<b) -> '<b |]
      -= \mv callback -> MV.withMVar (unMVar mv) (vapp callback),
    pfun 1 "modify_"
                 -: [$ty| all '<a. '<a mvar -> ('<a -> '<a) -> unit |]
      -= \mv callback -> MV.modifyMVar_ (unMVar mv) (vapp callback),
    pfun 1 "modify"
                 -: [$ty| all '<a '<b. '<a mvar -> ('<a -> '<a * '<b) -> '<b |]
      -= \mv callback -> MV.modifyMVar (unMVar mv) $ \v -> do
                           result <- vapp callback v
                           (vprjM result :: IO (Value, Value))
  ]

