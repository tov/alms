module Basis.Exn ( entries ) where

import BasisUtils
import Value
import AST

import qualified Data.Loc

import Control.Exception

entries :: [Entry Raw]
entries = [
    fun "raise" -: [ty| all `a. exn -> `a |]
      -= \exn -> throw (VExn exn :: VExn)
                 :: IO Value,
    fun "tryfun_string"
                -: [ty| all `a. (unit -o `a) -> (exn + string) + `a |]
      -= \f -> do
           fmap Right (vapp f vaUnit) `catches`
             [ Handler $ \(VExn v) -> return (Left (Left v))
             , Handler $ \e -> return (Left (Right (show (e:: IOError)))) ]
  ]
