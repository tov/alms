module Util (
  fromJust, (?:),
  foldrM, anyM, allM, anyM2, allM2,
  foldl2, foldr2, all2, any2,
  char2integer, integer2char,
  unscanr, unscanl,
  module Control.Monad
) where

import Data.Char (chr, ord)
import Data.Maybe (fromJust)
import Control.Monad

foldrM :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
foldrM _ z []     = return z
foldrM f z (b:bs) = foldrM f z bs >>= flip f b

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM p (x:xs) = do
  b <- p x
  if b
    then return True
    else anyM p xs
anyM _    _      = return False

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM p = liftM not . anyM (liftM not . p)

anyM2 :: Monad m => (a -> b -> m Bool) -> [a] -> [b] -> m Bool
anyM2 p as bs = anyM (uncurry p) (zip as bs)

allM2 :: Monad m => (a -> b -> m Bool) -> [a] -> [b] -> m Bool
allM2 p as bs = allM (uncurry p) (zip as bs)

foldl2 :: (c -> a -> b -> c) -> c -> [a] -> [b] -> c
foldl2 f z (x:xs) (y:ys) = foldl2 f (f z x y) xs ys
foldl2 _ z _      _      = z

foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
foldr2 f z (x:xs) (y:ys) = f x y (foldr2 f z xs ys)
foldr2 _ z _      _      = z

all2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
all2 p xs ys = and (zipWith p xs ys)

any2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
any2 p xs ys = or (zipWith p xs ys)

char2integer :: Char -> Integer
char2integer  = fromIntegral . ord

integer2char :: Integer -> Char
integer2char  = chr . fromIntegral

(?:) :: Maybe a -> [a] -> [a]
Nothing ?: xs = xs
Just x  ?: xs = x : xs

infixr 5 ?:

unscanr :: (b -> Maybe (a, b)) -> b -> ([a], b)
unscanr f b = case f b of
  Just (a, b') -> (a : fst rest, snd rest) where rest = unscanr f b'
  Nothing      -> ([], b)

unscanl :: (b -> Maybe (a, b)) -> b -> ([a], b)
unscanl f = loop [] where
  loop acc b = case f b of
    Just (a, b') -> loop (a : acc) b'
    Nothing      -> (acc, b)
