{-# LANGUAGE
      DeriveDataTypeable,
      QuasiQuotes #-}
module Basis.Future (entries) where

import Data.Typeable (Typeable)
import BasisUtils
import Syntax
import Value (Value, Valuable(..))

import qualified Syntax.Notable
import qualified Syntax.Decl
import qualified Data.Loc

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.MVar as MV

newtype Future = Future { unFuture :: MV.MVar Value }
  deriving (Eq, Typeable)

instance Valuable Future where
  veq = (==)
  vppr _ = text "#<(co)future>"


entries :: [Entry Raw]
entries  = [
    -- Futures
    dec [$dc| type +`a future qualifier A |],
    dec [$dc| type -`a cofuture qualifier A |],

    fun "new" -: [$ty| all `a. (unit -o `a) -> `a future |]
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f () >>= MV.putMVar future)
            return (Future future),
    fun "sync" -: [$ty| all `a. `a future -> `a |]
      -= (MV.takeMVar . unFuture),
    fun "coNew" -: [$ty| all `a. (`a future -o unit) -> `a cofuture |]
      -= \f -> do
            future <- MV.newEmptyMVar
            CC.forkIO (vapp f (Future future) >> return ())
            return (Future future),
    fun "coSync" -: [$ty| all `a. `a cofuture -> `a -o unit |]
      -= \future value -> MV.putMVar (unFuture future) value,
    fun "newPair" -: [$ty| all `a. unit -> `a future * `a cofuture |]
      -= \() -> do
            future <- MV.newEmptyMVar
            return (Future future, Future future)
  ]

