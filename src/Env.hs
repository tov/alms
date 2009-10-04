{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      FunctionalDependencies,
      MultiParamTypeClasses,
      UndecidableInstances #-}
module Env (
  Env(unEnv),
  Keyable(..),
  PathLookup(..), PathExtend(..), PathRemove(..),
  empty, isEmpty,
  (=:=), (=::=), (=:+=), (=+=), (=-=), (=--=), (=.=), (=|=),
  mapEnv, mapAccum, mapAccumM,
  toList, fromList, contents
) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Generics (Typeable, Data)
import Data.Monoid

infix 6 =:=, =::=, =.=
infixr 5 =+=
infixl 5 =-=, =--=, =|=

newtype Env v a = Env { unEnv:: M.Map v a }
  deriving (Typeable, Data)

class (Ord x, Ord y) => Keyable x y where
  liftKey :: y -> x
  liftEnv :: Env y a -> Env x a
  liftEnv (Env m) = Env (M.mapKeys liftKey m)

instance Keyable [Char] [Char] where
  liftKey = id

empty    :: Env v a
empty     = Env M.empty

isEmpty  :: Env v a -> Bool
isEmpty   = M.null . unEnv

-- singleton bind
(=:=)    :: Ord v => v -> a -> Env v a
v =:= a   = Env (M.singleton v a)

-- monad bind
(=::=)  :: (Monad m, Ord v) => v -> a -> Env v (m a)
x =::= v = x =:= return v

(=:+=)   :: Keyable v v => v -> v -> Env v v
v =:+= v' = v =:= v' =+= v' =:= v'

-- union
(=+=)    :: Keyable x y => Env x a -> Env y a -> Env x a
m =+= n   = m `mappend` liftEnv n

-- difference
(=-=)    :: Keyable x y => Env x a -> y -> Env x a
m =-= y   = Env (M.delete (liftKey y) (unEnv m))

(=--=)   :: Keyable x y => Env x a -> S.Set y -> Env x a
m =--= ys = Env (S.fold (M.delete . liftKey) (unEnv m) ys)

-- lookup
(=.=)    :: Keyable x y => Env x a -> y -> Maybe a
m =.= y   = M.lookup (liftKey y) (unEnv m)

-- intersection
(=|=)    :: Keyable x y => Env x a -> Env y b -> Env x (a, b)
m =|= n   = Env (M.intersectionWith (,) (unEnv m) (unEnv (liftEnv n)))

mapEnv :: Ord v => (a -> b) -> Env v a -> Env v b
mapEnv f = Env . M.map f . unEnv

mapAccum :: Ord v => (a -> b -> (b, c)) -> b -> Env v a -> (b, Env v c)
mapAccum f z m = case M.mapAccum (flip f) z (unEnv m) of
                   (c, m') -> (c, Env m')

mapAccumM :: (Ord v, Monad m) =>
             (a -> b -> m (b, c)) -> b -> Env v a -> m (b, Env v c)
mapAccumM f z m = do
  (c, l') <- helper z [] (M.toAscList (unEnv m))
  return (c, Env (M.fromDistinctAscList (reverse l')))
  where
    helper u acc [] = return (u, acc)
    helper u acc ((v, a):rest) = do
      (b, c) <- f a u
      helper b ((v, c) : acc) rest

toList   :: Ord x => Env x a -> [(x, a)]
toList    = M.toList . unEnv

fromList :: Ord x => [(x, a)] -> Env x a
fromList  = Env . M.fromList

contents :: Ord v => Env v a -> [a]
contents  = M.elems . unEnv

instance Ord v => Monoid (Env v a) where
  mempty      = empty
  mappend m n = Env (M.unionWith (\_ x -> x) (unEnv m) (unEnv n))

instance (Ord v, Show v, Show a) => Show (Env v a) where
  showsPrec _ env = foldr (.) id
    [ shows v . (" : "++) . shows a . ('\n':)
    | (v, a) <- M.toList (unEnv env) ]

instance Keyable k k' => PathLookup (Env k v) k' v where
  (=..=) = (=.=)

class PathLookup e k v | e k -> v where
  (=..=) :: e -> k -> Maybe v

instance PathLookup e k v => PathLookup [e] k v where
  []     =..= _ = Nothing
  (s:ss) =..= k = case s =..= k of
                    Just a  -> return a
                    Nothing -> ss =..= k

class PathExtend e e' where
  (=++=)   :: e -> e' -> e

instance Keyable k k' => PathExtend (Env k v) (Env k' v) where
  (=++=) = (=+=)

instance PathExtend e e' => PathExtend [e] e' where
  []     =++= _  = []
  (e:es) =++= e' = (e =++= e') : es

class PathRemove e k where
  (=\=)  :: e -> k -> e
  (=\\=) :: e -> S.Set k -> e
  e =\\= set = foldl (=\=) e (S.toList set)

instance PathRemove e k => PathRemove [e] k where
  es =\= k = map (=\= k) es

instance Keyable k k' => PathRemove (Env k v) k' where
  (=\=) = (=-=)

infix 6 =..=
infixr 5 =++=
infixl 5 =\=, =\\=
