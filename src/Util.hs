-- | Utility functions
module Util (
  -- * Extra collection operations
  -- ** Shallow mapping of 'Traversable's
  mapHead, mapTail, mapInit, mapLast,
  -- ** 'Foldable'/'Applicative' operations
  allA, anyA,
  -- ** 2-way 'Foldable' operations
  foldl2, foldr2, all2, any2,
  allA2, anyA2,
  -- ** Extra zips
  zip4, unzip4, zip5, unzip5,
  -- ** List operations
  mapCons, foldM1,
  lookupWithIndex, listNth, ordNub, partitionJust,
  -- *** Unfold with an accumulator
  unscanr, unscanl,
  -- *** Map in CPS
  mapCont, mapCont_,

  -- * Extra monadic operations
  whenM, unlessM, concatMapM, before,

  -- * Maps for state-like monads
  mapListen2, mapListen3,

  -- * 'Maybe' and 'Either' operations
  fromOptA, unEither,

  -- * More convenience
  -- ** Maybe functions
  (?:),
  -- ** Either funtions
  isLeft, isRight,
  -- ** List functions
  splitBy,
  -- ** Monomorphic @ord@ and @chr@
  char2integer, integer2char,
  -- ** For defining 'Ord'
  thenCmp, thenCmpM,
  -- ** Versions of fmap and compose
  (>>!),
  (<$$>), (<$$$>), (<$$$$>), (<$$$$$>), (<$$$$$$>),
  (<$.>), (<$$.>), (<$$$.>), (<$$$$.>),
  (<->), (<-->), (<--->), (<---->), (<----->),

  -- * Generic set operations
  SetLike(..), SetLike2(..),

  -- * Re-exports
  module Control.Arrow,
  module Control.Applicative,
  module Control.Monad,
  module Control.Monad.Error,
  module Control.Monad.Identity,
  module Control.Monad.List,
  module Control.Monad.RWS.Strict,
  module Control.Monad.Reader,
  module Control.Monad.State.Strict,
  module Control.Monad.Trans,
  module Control.Monad.Writer.Strict,
  module Data.Foldable,
  module Data.Function,
  module Data.Maybe,
  module Data.Monoid,
  module Data.Traversable,
  module Data.Tuple.All,
  module Data.OptionalClass,
  module Data.Perhaps,
  module Util.Bogus,
  module Util.Viewable,
  module Prelude,
) where

import Prelude hiding ( (=<<), Functor(..), Maybe(..), Monad(..), all,
                        and, any, concat, concatMap, elem, foldl, foldl1,
                        foldr, foldr1, mapM, mapM_, maximum, maybe,
                        minimum, notElem, or, product, sequence, sequence_,
                        sum )

import Control.Arrow ( Arrow(..), ArrowChoice(..), (>>>), (<<<) )
import Control.Applicative hiding ( empty )
import Control.Monad hiding ( forM, forM_, mapM_, mapM, msum,
                              sequence, sequence_ )

import Control.Monad.Error    ( MonadError(..), ErrorT(..), mapErrorT,
                                Error(..) )
import Control.Monad.Identity ( Identity(..) )
import Control.Monad.List     ( ListT(..), mapListT )
import Control.Monad.RWS.Strict ( RWST(..), runRWST, execRWST, evalRWST,
                                  mapRWST, evalRWS )
import Control.Monad.Reader     ( MonadReader(..), ReaderT(..), mapReaderT,
                                  asks, runReader )
import Control.Monad.State.Strict ( MonadState(..), StateT(..), evalStateT,
                                    execStateT, evalState, gets, modify,
                                    mapStateT )
import Control.Monad.Trans    ( MonadTrans(..), MonadIO(..) )
import Control.Monad.Writer.Strict ( MonadWriter(..), WriterT(..),
                                     runWriter, execWriterT, execWriter,
                                     mapWriterT, censor, listens )

import Data.Char (chr, ord)
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Foldable
import Data.Function ( on )
import Data.Traversable
import Data.Tuple.All

import Data.OptionalClass
import Data.Perhaps
import Util.Bogus
import Util.Viewable

import qualified Data.Set  as S
import qualified Data.List as L

mapHead, mapTail, mapInit, mapLast ∷ Traversable t ⇒ (a → a) → t a → t a

mapHead f = snd . mapAccumL each True where
  each True x = (False, f x)
  each _    x = (False, x)

mapTail f = snd . mapAccumL each True where
  each True x = (False, x)
  each _    x = (False, f x)

mapInit f = snd . mapAccumR each True where
  each True x = (False, x)
  each _    x = (False, f x)

mapLast f = snd . mapAccumR each True where
  each True x = (False, f x)
  each _    x = (False, x)

-- | 'all' with an applicative predicate
allA ∷ (Applicative f, Foldable t) ⇒ (a → f Bool) → t a → f Bool
allA p xs = and <$> traverse p (toList xs)

-- | 'any' with an applicative predicate
anyA ∷ (Applicative f, Foldable t) ⇒ (a → f Bool) → t a → f Bool
anyA p xs = or <$> traverse p (toList xs)

-- | Left-associative fold over two lists
foldl2 ∷ (Foldable t1, Foldable t2) ⇒
         (c → a → b → c) → c → t1 a → t2 b → c
foldl2 f z xs ys = foldl (uncurry . f) z (zip (toList xs) (toList ys))

-- | Right-associative fold over two lists
foldr2 ∷ (Foldable t1, Foldable t2) ⇒
         (a → b → c → c) → c → t1 a → t2 b → c
foldr2 f z xs ys = foldr (uncurry f) z (zip (toList xs) (toList ys))

-- | Two-list 'all'
all2 :: (Foldable f1, Foldable f2) ⇒
        (a -> b -> Bool) -> f1 a -> f2 b -> Bool
all2 p xs ys = and (zipWith p (toList xs) (toList ys))

-- | Two-list 'any'
any2 :: (Foldable f1, Foldable f2) ⇒
        (a -> b -> Bool) -> f1 a -> f2 b -> Bool
any2 p xs ys = or (zipWith p (toList xs) (toList ys))

-- | 'all' for two 'Foldable's with an applicative predicate
allA2 ∷ (Applicative f, Foldable t1, Foldable t2) ⇒
        (a → b → f Bool) → t1 a → t2 b → f Bool
allA2 p xs ys = allA id (zipWith p (toList xs) (toList ys))

-- | 'all' for two 'Foldable's with an applicative predicate
anyA2 ∷ (Applicative f, Foldable t1, Foldable t2) ⇒
        (a → b → f Bool) → t1 a → t2 b → f Bool
anyA2 p xs ys = anyA id (zipWith p (toList xs) (toList ys))

-- | Zip four lists
zip4   ∷ [a] → [b] → [c] → [d] → [(a, b, c, d)]
zip4 (a:as) (b:bs) (c:cs) (d:ds) = (a, b, c, d) : zip4 as bs cs ds
zip4 _      _      _      _      = []

-- | Zip five lists
zip5   ∷ [a] → [b] → [c] → [d] → [e] → [(a, b, c, d, e)]
zip5 (a:as) (b:bs) (c:cs) (d:ds) (e:es) = (a, b, c, d, e) : zip5 as bs cs ds es
zip5 _      _      _      _      _      = []

-- | Unzip four lists
unzip4 ∷ [(a, b, c, d)] → ([a], [b], [c], [d])
unzip4 = foldr (\(a,b,c,d) ~(as,bs,cs,ds) → (a:as,b:bs,c:cs,d:ds))
               ([],[],[],[])

-- | Unzip four lists
unzip5 ∷ [(a, b, c, d, e)] → ([a], [b], [c], [d], [e])
unzip5 = foldr (\(a,b,c,d,e) ~(as,bs,cs,ds,es) → (a:as,b:bs,c:cs,d:ds,e:es))
               ([],[],[],[],[])

-- | Apply one function to the head of a list and another to the
--   tail
mapCons :: (a -> b) -> ([a] -> [b]) -> [a] -> [b]
mapCons _  _  []     = []
mapCons fh ft (x:xs) = fh x : ft xs

-- | Fold over a non-empty 'Foldable' in a monad
foldM1          ∷ (Foldable t, Monad m) ⇒ (a → a → m a) → t a → m a
foldM1 f xs0    = loop (toList xs0) where
  loop []     = fail "foldM1: empty"
  loop (x:xs) = foldM f x xs

-- | Like 'Data.List.lookup', but returns the index into the list as
--   well.
lookupWithIndex ∷ Eq a ⇒ a → [(a, b)] → Maybe (b, Int)
lookupWithIndex k = loop 0 where
  loop _   []   = Nothing
  loop !ix ((k',v):rest)
    | k == k'   = Just (v, ix)
    | otherwise = loop (ix + 1) rest

-- | Safe version of '(Data.List.!!)'
listNth ∷ Int → [a] → Maybe a
listNth i = foldr (const . Just) Nothing . drop i

-- | Like nub, but O(n log n) instead of O(n^2)
ordNub ∷ Ord a ⇒ [a] → [a]
ordNub = loop S.empty where
  loop seen (x:xs)
    | x `S.member` seen = loop seen xs
    | otherwise         = x : loop (S.insert x seen) xs
  loop _    []     = []

-- | Partition a list into the portions where the function returns
--   'Just' and the portions where it returns 'Nothing'
partitionJust ∷ (a → Maybe b) → [a] → ([a], [b])
partitionJust f = foldr each ([], []) where
  each x (xs, ys) = case f x of
    Nothing → (x:xs, ys)
    Just y →  (xs, y:ys)

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

whenM ∷ Monad m ⇒ m Bool → m () → m ()
whenM test branch = test >>= flip when branch

unlessM ∷ Monad m ⇒ m Bool → m () → m ()
unlessM test branch = test >>= flip unless branch

-- | Map and concatenate in a monad.
concatMapM   ∷ (Foldable t, Monad m, Monoid b) ⇒ (a → m b) → t a → m b
concatMapM f = foldr (liftM2 mappend . f) (return mempty)

before ∷ Monad m ⇒ m a → (a → m b) → m a
before m k = do
  a ← m
  k a
  return a

infixl 8 `before`

mapListen2 ∷ Monad m ⇒ (a → m ((b, s), w)) → a → m ((b, w), s)
mapListen3 ∷ Monad m ⇒ (a → m ((b, s1, s2), w)) → a → m ((b, w), s1, s2)

mapListen2 mapper action = do
  ((b, s), w) ← mapper action
  return ((b, w), s)

mapListen3 mapper action = do
  ((b, s1, s2), w) ← mapper action
  return ((b, w), s1, s2)

fromOptA ∷ (Applicative f, Optional t) ⇒ f a → t a → f a
fromOptA def = foldOpt def pure

unEither ∷ Either a a → a
unEither = either id id

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
(?:) :: Optional t ⇒ t a -> [a] -> [a]
(?:)  = foldOpt id (:)

infixr 5 ?:

isLeft, isRight :: Either a b -> Bool
isLeft (Left _)   = True
isLeft _          = False
isRight (Right _) = True
isRight _         = False

-- | To combine two 'Ordering's in lexigraphic order
thenCmp :: Ordering -> Ordering -> Ordering
thenCmp EQ k2 = k2
thenCmp k1 _  = k1

-- | To combine two actions producing 'Ordering's in lexigraphic order
thenCmpM ∷ Monad m ⇒ m Ordering → m Ordering → m Ordering
thenCmpM m1 m2 = do
  ordering ← m1
  case ordering of
    EQ → m2
    _  → return ordering

infixr 4 `thenCmp`, `thenCmpM`

-- | @flip fmap@
(>>!) :: Functor f => f a -> (a -> b) -> f b
(>>!)  = flip fmap

infixl 1 >>!

(<$$>) ∷ (Functor f, Functor g) ⇒ 
         (b → c) → g (f b) → g (f c)
(<$$>) = fmap . fmap

(<$$$>) ∷ (Functor f, Functor g, Functor h) ⇒
          (b → c) → h (g (f b)) →
          h (g (f c))
(<$$$>) = fmap . fmap . fmap

(<$$$$>) ∷ (Functor f, Functor g, Functor h, Functor i) ⇒
           (b → c) → i (h (g (f b))) →
           i (h (g (f c)))
(<$$$$>) = fmap . fmap . fmap . fmap

(<$$$$$>) ∷ (Functor f, Functor g, Functor h, Functor i, Functor j) ⇒
            (b → c) → j (i (h (g (f b)))) →
            j (i (h (g (f c))))
(<$$$$$>) = fmap . fmap . fmap . fmap . fmap

(<$$$$$$>) ∷ (Functor f, Functor g, Functor h,
              Functor i, Functor j, Functor k) ⇒
             (b → c) → k (j (i (h (g (f b))))) →
             k (j (i (h (g (f c)))))
(<$$$$$$>) = fmap . fmap . fmap . fmap . fmap . fmap

infixl 4 <$$>, <$$$>, <$$$$>, <$$$$$>, <$$$$$$>

(<$.>) ∷ (Arrow (⇝), Functor f) ⇒
         f (b ⇝ c) → (a ⇝ b) →
         f (a ⇝ c)
f <$.> g = (g >>>) <$> f

(<$$.>) ∷ (Arrow (⇝), Functor f, Functor g) ⇒
          g (f (b ⇝ c)) → (a ⇝ b) →
          g (f (a ⇝ c))
f <$$.> g = (g >>>) <$$> f

(<$$$.>) ∷ (Arrow (⇝), Functor f, Functor g, Functor h) ⇒
           h (g (f (b ⇝ c))) → (a ⇝ b) →
           h (g (f (a ⇝ c)))
f <$$$.> g = (g >>>) <$$$> f

(<$$$$.>) ∷ (Arrow (⇝), Functor f, Functor g, Functor h, Functor i) ⇒
            i (h (g (f (b ⇝ c)))) → (a ⇝ b) →
            i (h (g (f (a ⇝ c))))
f <$$$$.> g = (g >>>) <$$$$> f

infixl 4 <$.>, <$$.>, <$$$.>, <$$$$.>

(<->)   ∷ Functor f ⇒ 
          f (a → b) → a → f b
f <-> x = ($ x) <$> f

(<-->)   ∷ (Functor f, Functor g) ⇒
           f (g (a → b)) → a → f (g b)
f <--> x = (<-> x) <$> f

(<--->)   ∷ (Functor f, Functor g, Functor h) ⇒
            f (g (h (a → b))) → a → f (g (h b))
f <---> x = (<--> x) <$> f

(<---->)   ∷ (Functor f, Functor g, Functor h, Functor i) ⇒
             f (g (h (i (a → b)))) → a → f (g (h (i b)))
f <----> x = (<---> x) <$> f

(<----->)   ∷ (Functor f, Functor g, Functor h, Functor i, Functor j) ⇒
              f (g (h (i (j (a → b))))) → a → f (g (h (i (j b))))
f <-----> x = (<----> x) <$> f

infixl 4 <->, <-->, <--->, <---->, <----->

class (Eq a, Foldable t) ⇒ SetLike t a where
  isEmptySet    ∷ t a → Bool
  (∈), (∉)      ∷ a → t a → Bool
  emptySet      ∷ t a
  singleton     ∷ a → t a
  --
  isEmptySet    = null . toList
  a ∈ set       = a `elem` toList set
  a ∉ set       = not (a ∈ set)

class (SetLike t a, SetLike t' a) ⇒ SetLike2 t t' a where
  (⊆), (⊇), (/⊆), (/⊇), (/∩)
                ∷ t a → t' a → Bool
  (∪), (∩), (∖) ∷ t a → t' a → t a
  --
  set1 ⊆ set2   = all (∈ set2) set1
  set1 ⊇ set2   = all (∈ set1) set2
  set1 /⊆ set2  = not (set1 /⊆ set2)
  set1 /⊇ set2  = not (set1 /⊇ set2)
  set1 /∩ set2  = not (any (∈ set2) set1)

infix 4 ∈, ∉, ⊆, ⊇, /⊆, /⊇, /∩
infixl 6 ∪, ∖
infixl 7 ∩

instance Eq a ⇒ SetLike [] a where
  emptySet      = []
  singleton a   = [a]

instance Eq a ⇒ SetLike2 [] [] a where
  (∪)           = L.union
  (∩)           = L.intersect
  (∖)           = (L.\\)

instance Ord a ⇒ SetLike2 [] S.Set a where
  (∪)           = L.union <$.> toList
  (∩)           = L.intersect <$.> toList
  (∖)           = (L.\\) <$.> toList

instance Ord a ⇒ SetLike S.Set a where
  isEmptySet    = S.null
  (∈)           = S.member
  emptySet      = S.empty
  singleton     = S.singleton

instance Ord a ⇒ SetLike2 S.Set S.Set a where
  (⊆)           = S.isSubsetOf
  set1 /∩ set2  = isEmptySet (set1 ∩ set2)
  (∪)           = S.union
  (∩)           = S.intersection
  (∖)           = (S.\\)

instance Ord a ⇒ SetLike2 S.Set [] a where
  (⊆)           = (⊆) <$.> S.fromList
  set1 ⊇ list2  = all (∈ set1) list2
  set1 /∩ list2 = all (∉ set1) list2
  (∪)           = foldr S.insert
  (∩)           = (∩) <$.> S.fromList
  (∖)           = foldr S.delete
