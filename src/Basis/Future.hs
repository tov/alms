{-# LANGUAGE DeriveDataTypeable #-}
module Basis.Future (entries) where

import Data.Typeable (Typeable)
import BasisUtils
import Value (Value, Valuable(..))

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.MVar as MV

newtype Future = Future { unFuture :: MV.MVar Value }
  deriving (Eq, Typeable)

instance Valuable Future where
  veq = (==)
  vpprPrec _ _ = text "#<(co)future>"


entries :: [Entry]
entries  = [
    -- Futures
    typ "+'<a future qualifier A",
    typ "-'<a cofuture qualifier A",

    pfun 1 "new" -: "all '<a. (unit -o '<a) -> '<a future"
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f () >>= MV.putMVar future)
            return (Future future),
    pfun 1 "get" -: "all '<a. '<a future -> '<a"
      -= (MV.takeMVar . unFuture),
    pfun 1 "coNew" -: "all '<a. ('<a future -o unit) -> '<a cofuture"
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f (Future future) >> return ())
            return (Future future),
    pfun 1 "coPut" -: "all '<a. '<a cofuture -> '<a -o unit"
      -= \future value -> MV.putMVar (unFuture future) value
  ]

