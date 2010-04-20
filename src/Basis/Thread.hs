{-# LANGUAGE DeriveDataTypeable #-}
module Basis.Thread (entries) where

import qualified Control.Concurrent as CC
import BasisUtils
import Value (Vinj(..))
import Util

entries :: [Entry]
entries =  [
    -- Threads
    typ "thread",
    fun "fork" -: "(unit -> unit) -> thread"
      -= \f -> Vinj `fmap` CC.forkIO (vapp f () >> return ()),
    fun "kill" -: "thread -> unit"
      -= CC.killThread . unVinj,
    fun "delay" -: "int -> unit"
      -= CC.threadDelay . (fromIntegral :: Integer -> Int),
    fun "print" -: "thread -> thread"
      -= \t -> do print (t :: Vinj CC.ThreadId); return t
  ]
