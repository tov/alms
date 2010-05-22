{-# LANGUAGE
      QuasiQuotes #-}
module Basis.Exn ( entries ) where

import BasisUtils
import Value
import Syntax

import qualified Loc
import qualified Syntax.Notable

import Control.Exception

entries :: [Entry Raw]
entries = [
    fun "raise" -: [$ty| exn -> any |]
      -= \exn -> throw (VExn exn :: VExn)
                 :: IO Value,
    fun "tryfun_string"
                -: [$ty| all `a. (unit -o `a) -> (exn + string) + `a |]
      -= \(VaFun _ f) -> do
           fmap Right (f vaUnit) `catches`
             [ Handler $ \(VExn v) -> return (Left (Left v))
             , Handler $ \e -> return (Left (Right (show (e:: IOError)))) ]
  ]
