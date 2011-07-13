{-# LANGUAGE
      DeriveDataTypeable,
      QuasiQuotes #-}
module Basis.Array (entries) where

import Data.Typeable (Typeable)
import BasisUtils
import AST
import Util
import Value (Value, Valuable(..))

import qualified AST.Notable
import qualified AST.Decl
import qualified Data.Loc

import qualified Data.Array.IO as A

newtype Array = Array { unArray :: A.IOArray Int Value }
  deriving (Eq, Typeable)

instance Valuable Array where
  veq = (==)
  vppr _ = text "#<array>"

io :: IO a -> IO a
io  = id

entries :: [Entry Raw]
entries  = [
    dec [$dc| type `a array |],
    fun "build" -: [$ty| all `a. int -> (int -> `a) -> `a array |]
      -= \size builder -> io $ do
           a <- A.newArray_ (0, size - 1)
           forM_ [ 0 .. size - 1 ] $ \i ->
             vapp builder i >>= A.writeArray a i
           return (Array a),
    fun "size" -: [$ty| all `a. `a array -> int |]
      -= \a -> io $ do
            (_, limit) <- A.getBounds (unArray a)
            return (limit + 1),
    fun "swap" -: [$ty| all `a. `a array -> int -> `a -> `a |]
      -= \(Array a) ix new -> io $ do
            old <- A.readArray a ix
            A.writeArray a ix new
            return old,
    fun "get" -: [$ty| all 'a. 'a array -> int -> 'a |]
      -= \(Array a) ix -> io $ A.readArray a ix
  ]

