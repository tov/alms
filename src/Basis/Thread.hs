{-# LANGUAGE
      DeriveDataTypeable,
      QuasiQuotes #-}
module Basis.Thread (entries) where

import BasisUtils
import Syntax
import Value (Vinj(..))

import qualified Loc
import qualified Syntax.Notable
import qualified Syntax.Decl

import qualified Control.Concurrent as CC

entries :: [Entry]
entries =  [
    -- Threads
    dec [$dc| type thread |],
    fun "fork"  -: [$ty| (unit -> unit) -> thread |]
      -= \f -> Vinj `fmap` CC.forkIO (vapp f () >> return ()),
    fun "kill"  -: [$ty| thread -> unit |]
      -= CC.killThread . unVinj,
    fun "delay" -: [$ty| int -> unit |]
      -= CC.threadDelay . (fromIntegral :: Integer -> Int),
    fun "print" -: [$ty| thread -> thread |]
      -= \t -> do print (t :: Vinj CC.ThreadId); return t
  ]
