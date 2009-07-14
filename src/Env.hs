{-# LANGUAGE
      DeriveDataTypeable #-}
module Env (
  Env(unEnv),
  empty, isEmpty,
  (=:=), (=::=), (=+=), (=-=), (=--=), (=.=), (=|=),
  mapAccum, mapAccumM,
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

empty    :: Env v a
empty     = Env M.empty

isEmpty  :: Env v a -> Bool
isEmpty   = M.null . unEnv

-- singleton bind
(=:=)    :: Ord v => v -> a -> Env v a
v =:= a   = Env (M.singleton v a)

(=::=)  :: (Monad m, Ord v) => v -> a -> Env v (m a)
x =::= v = x =:= return v


-- union
(=+=)    :: Ord v => Env v a -> Env v a -> Env v a
m =+= n   = Env (M.unionWith (\_ x -> x) (unEnv m) (unEnv n)) where

-- difference
(=-=)    :: Ord v => Env v a -> v -> Env v a
m =-= v   = Env (M.delete v (unEnv m))

(=--=)   :: Ord v => Env v a -> S.Set v -> Env v a
m =--= vs = Env (S.fold M.delete (unEnv m) vs)

-- lookup
(=.=)    :: Ord v => Env v a -> v -> Maybe a
m =.= v   = M.lookup v (unEnv m)

-- intersection
(=|=)    :: Ord v => Env v a -> Env v b -> Env v (a, b)
m =|= n   = Env (M.intersectionWith (,) (unEnv m) (unEnv n))

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

toList   :: Ord v => Env v a -> [(v, a)]
toList    = M.toList . unEnv

fromList :: Ord v => [(v, a)] -> Env v a
fromList  = Env . M.fromList

contents :: Ord v => Env v a -> [a]
contents  = M.elems . unEnv

instance (Eq a, Ord v) => Monoid (Env v a) where
  mempty  = empty
  mappend = (=+=)

instance (Ord v, Show v, Show a) => Show (Env v a) where
  showsPrec _ env = foldr (.) id
    [ shows v . (" : "++) . shows a . ('\n':)
    | (v, a) <- M.toList (unEnv env) ]
