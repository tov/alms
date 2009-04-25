module Util (
  fromJust, foldl2, all2, char2integer, integer2char, (?:)
) where

import Data.Char (chr, ord)
import Data.Maybe (fromJust)

foldl2 :: (c -> a -> b -> c) -> c -> [a] -> [b] -> c
foldl2 f z (x:xs) (y:ys) = foldl2 f (f z x y) xs ys
foldl2 _ z _      _      = z

all2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
all2 p xs ys = and (zipWith p xs ys)

char2integer :: Char -> Integer
char2integer  = fromIntegral . ord

integer2char :: Integer -> Char
integer2char  = chr . fromIntegral

(?:) :: Maybe a -> [a] -> [a]
Nothing ?: xs = xs
Just x  ?: xs = x : xs

infixr 5 ?:
