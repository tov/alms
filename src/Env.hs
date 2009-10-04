{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      FunctionalDependencies,
      MultiParamTypeClasses,
      OverlappingInstances,
      ScopedTypeVariables,
      UndecidableInstances #-}
module Env {-(
  Env(unEnv),
  (:>:)(..),
  empty, isEmpty,
  (-:-), (-::-), (-:+-), (-+-), (-\-), (-\\-), (-.-), (-|-),
  mapEnv, mapAccum, mapAccumM,
  toList, fromList, contents-- ,
--   PathLookup(..), PathExtend(..), PathRemove(..),
)-} where

import Util
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Generics (Typeable, Data)
import Data.Monoid

infix 6 -:-, -::-, -:+-
infixl 6 -.-
infixr 5 -+-
infixl 5 -\-, -\\-, -|-

newtype Env k v = Env { unEnv:: M.Map k v }
  deriving (Typeable, Data)

-- Key subsumption.  Keys need to be
-- declared.
class (Ord x, Ord y) => x :>: y where
  liftKey :: y -> x
  liftEnv :: Env y v -> Env x v
  liftEnv (Env m) = Env (M.mapKeys liftKey m)

-- Reflexivity:
instance Ord k => (:>:) k k where
  liftKey = id

empty    :: Env k v
empty     = Env M.empty

isEmpty  :: Env k v -> Bool
isEmpty   = M.null . unEnv

-- singleton bind
(-:-)    :: Ord k => k -> v -> Env k v
k -:- v   = Env (M.singleton k v)

-- monad bind
(-::-)  :: (Monad m, Ord k) => k -> v -> Env k (m v)
k -::- v = k -:- return v

-- "closure bind"
(-:+-)   :: Ord k => k -> k -> Env k k
k -:+- k' = k -:- k' -+- k' -:- k'

-- union (right preference
(-+-)    :: (k :>: k') => Env k v -> Env k' v -> Env k v
m -+- n   = m `mappend` liftEnv n

-- difference
(-\-)    :: (k :>: k') => Env k v -> k' -> Env k v
m -\- y   = Env (M.delete (liftKey y) (unEnv m))

(-\\-)   :: (k :>: k') => Env k v -> S.Set k' -> Env k v
m -\\- ys = Env (S.fold (M.delete . liftKey) (unEnv m) ys)

-- lookup
(-.-)    :: (k :>: k') => Env k v -> k' -> Maybe v
m -.- y   = M.lookup (liftKey y) (unEnv m)

-- intersection
(-|-)    :: (k :>: k') => Env k v -> Env k' w -> Env k (v, w)
m -|- n   = Env (M.intersectionWith (,) (unEnv m) (unEnv (liftEnv n)))

mapEnv :: Ord k => (v -> w) -> Env k v -> Env k w
mapEnv f = Env . M.map f . unEnv

mapAccum :: Ord k => (v -> a -> (a, w)) -> a -> Env k v -> (a, Env k w)
mapAccum f z m = case M.mapAccum (flip f) z (unEnv m) of
                   (w, m') -> (w, Env m')

mapAccumM :: (Ord k, Monad m) =>
             (v -> a -> m (a, w)) -> a -> Env k v -> m (a, Env k w)
mapAccumM f z m = do
  (a, elts) <- helper z [] (M.toAscList (unEnv m))
  return (a, Env (M.fromDistinctAscList (reverse elts)))
  where
    helper a acc [] = return (a, acc)
    helper a acc ((k, v):rest) = do
      (a', w) <- f v a
      helper a' ((k, w) : acc) rest

toList   :: Ord k => Env k v -> [(k, v)]
toList    = M.toList . unEnv

fromList :: Ord k => [(k, v)] -> Env k v
fromList  = Env . M.fromList

contents :: Ord k => Env k v -> [v]
contents  = M.elems . unEnv

instance Ord k => Monoid (Env k v) where
  mempty      = empty
  mappend m n = Env (M.unionWith (\_ v -> v) (unEnv m) (unEnv n))

instance (Ord k, Show k, Show v) => Show (Env k v) where
  showsPrec _ env = foldr (.) id
    [ shows k . (" : "++) . shows v . ('\n':)
    | (k, v) <- M.toList (unEnv env) ]

class GenExtend e e' where
  (=+=) :: e -> e' -> e

class GenRemove e k where
  (=\=)  :: e -> k -> e
  (=\\=) :: e -> S.Set k -> e
  e =\\= set = foldl (=\=) e (S.toList set)

class GenLookup e k v | e k -> v where
  (=..=) :: e -> k -> Maybe v

class GenModify e k v where
  genModify :: e -> k -> (v -> v) -> e

class GenEmpty e where
  genEmpty :: e

instance GenLookup e k v => GenLookup (Maybe e) k v where
  Just e  =..= k  = e =..= k
  Nothing =..= _  = Nothing

(=:=)  :: Ord k => k -> v -> Env k v
(=::=) :: (Ord k, Monad m) => k -> v -> Env k (m v)
(=:+=) :: Ord k => k -> k -> Env k k
(=:=)   = (-:-)
(=::=)  = (-::-)
(=:+=)  = (-:+-)

infix 6 =:=, =::=, =:+=
infixl 6 =.=, =..=
infixr 5 =+=, =++=
infixl 5 =\=, =\\=

instance (k :>: k') => GenExtend (Env k v) (Env k' v)    where (=+=) = (-+-)
instance Ord k      => GenRemove (Env k v) k             where (=\=) = (-\-)
instance (k :>: k') => GenLookup (Env k v) k' v          where (=..=) = (-.-)
instance (k :>: k') => GenModify (Env k v) k' v where
  genModify e k fv = case e =..= k of
    Nothing -> e
    Just v  -> e =+= k -:- fv v
instance GenEmpty (Env k v) where genEmpty = empty

data NEnv p e = NEnv {
                  envenv :: Env p (NEnv p e),
                  valenv :: e
                }
  deriving Show

data Qual p k = Q {
                  qualpath :: [p],
                  qualname :: k
                }
  deriving (Eq, Ord, Show)

instance GenEmpty e => GenEmpty (NEnv p e) where
  genEmpty = NEnv genEmpty genEmpty

-- We can extend a nested env with
--  - some subenvs
--  - a value env
--  - another nested env (preferring the right)
--  - (=++=) unions subenvs rather than replacing
instance Ord p => GenExtend (NEnv p e) (Env p (NEnv p e)) where
  nenv =+= e = nenv { envenv = envenv nenv =+= e }

instance Ord p => GenExtend (NEnv p e) (Env p e) where
  nenv =+= e = nenv =+= mapEnv (NEnv (empty :: Env p (NEnv p e))) e

instance GenExtend e e => GenExtend (NEnv p e) e where
  nenv =+= e = nenv { valenv = valenv nenv =+= e }

instance (Ord p, GenExtend e e) =>
         GenExtend (NEnv p e) (NEnv p e) where
  NEnv es vs =+= NEnv es' vs' = NEnv (es =+= es') (vs =+= vs')

-- tree-wise union:
(=++=) :: (Ord p, GenExtend e e) => NEnv p e -> NEnv p e -> NEnv p e
NEnv (Env m) e =++= NEnv (Env m') e' =
  NEnv (Env (M.unionWith (=++=) m m')) (e =+= e')

-- We can lookup in a nested env by
--  - one path component
--  - one key
--  - a path
--  - a path to a key
instance Ord p => GenLookup (NEnv p e) p (NEnv p e) where
  nenv =..= p = envenv nenv =..= p

instance Ord p => GenLookup (NEnv p e) [p] (NEnv p e) where
  (=..=) = foldM (=..=)

instance (Ord p, GenLookup e k v) =>
         GenLookup (NEnv p e) (Qual p k) v where
  nenv =..= Q path k = nenv =..= path >>= (=.= k)

-- look up a simple key
(=.=) :: GenLookup e k v => NEnv p e -> k -> Maybe v
nenv =.= k = valenv nenv =..= k

-- We can modify a nested env at
--  - one path component
--  - a path to a nested env
--  - a path to an env
--  - a path to a key

instance Ord p => GenModify (NEnv p e) p (NEnv p e) where
  genModify nenv p f  =  genModify nenv [p] f

instance Ord p => GenModify (NEnv p e) [p] (NEnv p e) where
  genModify nenv [] f     = f nenv
  genModify nenv (p:ps) f = case envenv nenv =..= p of
    Nothing    -> nenv
    Just nenv' -> nenv =+= p =:= genModify nenv' ps f

instance Ord p => GenModify (NEnv p e) [p] e where
  genModify nenv path fe = genModify nenv path fnenv where
    fnenv      :: NEnv p e -> NEnv p e
    fnenv nenv' = nenv' { valenv = fe (valenv nenv') }

instance (Ord p, GenModify e k v) =>
         GenModify (NEnv p e) (Qual p k) v where
  genModify nenv (Q path k) fv = genModify nenv path fe where
    fe  :: e -> e
    fe e = genModify e k fv

-- we can remove at
--  - a single path component
--  - a path to a key
--  - a path to a path
instance Ord p => GenRemove (NEnv p e) p where
  nenv =\= p = nenv { envenv = envenv nenv =\= p }

instance (Ord p, GenRemove e k) => GenRemove (NEnv p e) (Qual p k) where
  nenv =\= Q path k = genModify nenv path fe where
    fe :: e -> e
    fe  = (=\= k)

instance Ord p => GenRemove (NEnv p e) (Qual p p) where
  nenv =\= Q path p = genModify nenv path fnenv where
    fnenv :: NEnv p e -> NEnv p e
    fnenv  = (=\= p)

