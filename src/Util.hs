-- | Utility functions
{-# LANGUAGE FlexibleContexts #-}
module Util (
  -- * List combinators
  -- ** Two-list versions
  foldl2, foldr2, all2, any2,
  -- ** Monadic version
  foldrM, anyM, allM, anyM2, allM2,
  -- ** Unfold with an accumulator
  unscanr, unscanl,
  -- ** Map in CPS
  mapCont, mapCont_,
  -- ** Monad generalization of map and sequence
  GSequence(..),

  -- * More convenience
  -- ** Maybe functions
  fromJust, (?:),
  -- ** List functions
  splitBy,
  -- ** Monomorphic @ord@ and @chr@
  char2integer, integer2char,
  -- ** @flip fmap@
  (>>!),

  -- * Re-exports
  module Control.Arrow,
  module Control.Monad,
  module Control.Applicative
) where

import Data.Char (chr, ord)
import Data.Maybe (fromJust)
import Control.Arrow hiding (loop, (<+>))
import Control.Monad
import Control.Applicative (Applicative(..), (<$>), (<$), (<**>))

-- | Right-associative monadic fold
foldrM :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
foldrM _ z []     = return z
foldrM f z (b:bs) = foldrM f z bs >>= flip f b

-- | Like 'Prelude.any' with a monadic predicate
anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM p (x:xs) = do
  b <- p x
  if b
    then return True
    else anyM p xs
anyM _    _      = return False

-- | Like 'Prelude.all' with a monadic predicate
allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM p = liftM not . anyM (liftM not . p)

-- | Two-list, monadic 'any'
anyM2 :: Monad m => (a -> b -> m Bool) -> [a] -> [b] -> m Bool
anyM2 p as bs = anyM (uncurry p) (zip as bs)

-- | Two-list, monadic 'all'
allM2 :: Monad m => (a -> b -> m Bool) -> [a] -> [b] -> m Bool
allM2 p as bs = allM (uncurry p) (zip as bs)

-- | Left-associative fold over two lists
foldl2 :: (c -> a -> b -> c) -> c -> [a] -> [b] -> c
foldl2 f z (x:xs) (y:ys) = foldl2 f (f z x y) xs ys
foldl2 _ z _      _      = z

-- | Right-associative fold over two lists
foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
foldr2 f z (x:xs) (y:ys) = f x y (foldr2 f z xs ys)
foldr2 _ z _      _      = z

-- | Two-list 'all'
all2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
all2 p xs ys = and (zipWith p xs ys)

-- | Two-list 'any'
any2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
any2 p xs ys = or (zipWith p xs ys)

-- | The ASCII value of a character
char2integer :: Char -> Integer
char2integer  = fromIntegral . ord

-- | The character of an ASCII value
integer2char :: Integer -> Char
integer2char  = chr . fromIntegral

-- | Break a list where the given preducate answers true
splitBy :: (a -> Bool) -> [a] -> [[a]]
splitBy _ [] = []
splitBy p xs = let (ys, zs) = break p xs 
                in ys : splitBy p (drop 1 zs)

-- | Maybe cons, maybe not
(?:) :: Maybe a -> [a] -> [a]
Nothing ?: xs = xs
Just x  ?: xs = x : xs

infixr 5 ?:

-- | Unfold a list, left-to-right, returning the final state
unscanr :: (b -> Maybe (a, b)) -> b -> ([a], b)
unscanr f b = case f b of
  Just (a, b') -> (a : fst rest, snd rest) where rest = unscanr f b'
  Nothing      -> ([], b)

-- | Unfold a list, right-to-left, returning the final state
unscanl :: (b -> Maybe (a, b)) -> b -> ([a], b)
unscanl f = loop [] where
  loop acc b = case f b of
    Just (a, b') -> loop (a : acc) b'
    Nothing      -> (acc, b)

-- | @flip fmap@
(>>!) :: Functor f => f a -> (a -> b) -> f b
(>>!)  = flip fmap

infixl 1 >>!

-- | CPS version of 'map'
mapCont :: (a -> (b -> r) -> r) -> [a] -> ([b] -> r) -> r
mapCont _ []     k = k []
mapCont f (x:xs) k = f x $ \x' ->
                     mapCont f xs $ \xs' ->
                       k (x' : xs')

-- | CPS version of 'map_'
mapCont_ :: (a -> r -> r) -> [a] -> r -> r
mapCont_ _ []     k = k
mapCont_ f (x:xs) k = f x $ mapCont_ f xs $ k

-- | Generalize 'map' and 'sequence' to a few other monads
class GSequence m where
  gsequence   :: Monad m' => m (m' a) -> m' (m a)
  gsequence_  :: Monad m' => m (m' a) -> m' ()
  gsequence_ m = gsequence m >> return ()
  gmapM       :: (Monad m, Monad m') => (a -> m' b) -> m a -> m' (m b)
  gmapM f      = gsequence . liftM f
  gmapM_      :: (Monad m, Monad m') => (a -> m' b) -> m a -> m' ()
  gmapM_ f     = gsequence_ . liftM f
  gforM       :: (Monad m, Monad m') => m a -> (a -> m' b) -> m' (m b)
  gforM        = flip gmapM
  gforM_      :: (Monad m, Monad m') => m a -> (a -> m' b) -> m' ()
  gforM_       = flip gmapM_

instance GSequence [] where
  gsequence  = sequence
  gsequence_ = sequence_
  gmapM      = mapM
  gmapM_     = mapM_

instance GSequence Maybe where
  gsequence  = maybe (return Nothing) (liftM return)
  gsequence_ = maybe (return ()) (>> return ())

