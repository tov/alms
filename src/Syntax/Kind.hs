{-# LANGUAGE
      DeriveDataTypeable #-}
module Syntax.Kind (
  -- * Qualifiers, qualifiers sets, and variance
  Q(..), QualSet(..), Variance(..),
  -- ** Qualifier operations
  qsConst, qsVar, qsVars, qsFromListM, qsFromList, qsToList,
) where

import Syntax.POClass
import Util

import Control.Monad.Identity (runIdentity)
import Data.List (elemIndex, union, intersect)
import Data.Generics (Typeable(..), Data(..))

-- QUALIFIERS, VARIANCES

-- | Usage qualifiers
data Q
  -- | affine
  = Qa
  -- | unlimited
  | Qu
  deriving (Eq, Typeable, Data)

-- |
-- Determines how the parameters to a tycon contribute to
-- the qualifier of the type:
--   if @qualset c = QualSet q set@ then
--
-- @
--    |(t1, ..., tk) c| = q \\sqcup \\bigsqcup { qi | i <- set }
-- @
data QualSet = QualSet Q [Int]
  deriving (Typeable, Data)

-- | Tycon parameter variance (like sign analysis)
data Variance
  -- | Z
  = Invariant
  -- | non-negative
  | Covariant
  -- | non-positive
  | Contravariant
  -- | { 0 } 
  | Omnivariant
  deriving (Eq, Ord, Typeable, Data)

qsConst :: Q -> QualSet
qsConst  = flip QualSet []

qsVar   :: Int -> QualSet
qsVar    = qsVars . return

qsVars  :: [Int] -> QualSet
qsVars   = QualSet minBound

qsFromListM :: (Eq tv, Monad m) => (tv -> m QualSet) ->
               [tv] -> [Either tv Q] -> m QualSet
qsFromListM unbound tvs qs = bigVee `liftM` mapM each qs where
  each (Left tv) = case tv `elemIndex` tvs of
    Nothing -> unbound tv
    Just n  -> return (qsVar n)
  each (Right q) = return (qsConst q)

qsFromList :: Eq tv => [tv] -> [Either tv Q] -> QualSet
qsFromList tvs qs = runIdentity (qsFromListM (\_ -> return minBound) tvs qs)

qsToList   :: Eq tv => [tv] -> QualSet -> [Either tv Q]
qsToList _ qs | qs == minBound
  = []
qsToList tvs (QualSet q ixs) 
  = Right q : [ Left (tvs !! ix) | ix <- ixs ]

instance Show Q where
  showsPrec _ Qa = ('A':)
  showsPrec _ Qu = ('U':)

instance Show QualSet where
  show (QualSet q ixs) =
    show q ++ " \\/ bigVee " ++ show ixs

instance Show Variance where
  showsPrec _ Invariant     = ('1':)
  showsPrec _ Covariant     = ('+':)
  showsPrec _ Contravariant = ('-':)
  showsPrec _ Omnivariant   = ('0':)

instance Eq QualSet where
  QualSet q ixs == QualSet q' ixs'
    | q == maxBound && q' == maxBound = True
    | otherwise                       = q == q' && ixs == ixs'

instance Bounded Q where
  minBound = Qu
  maxBound = Qa

instance Bounded QualSet where
  minBound = QualSet minBound []
  maxBound = QualSet maxBound []

instance Bounded Variance where
  minBound = Omnivariant
  maxBound = Invariant

-- | The variance lattice:
--
-- @
--       (In)
--         T
--  (Co) +   - (Contra)
--         0
--      (Omni)
-- @
instance PO Variance where
  Covariant     \/ Covariant     = Covariant
  Contravariant \/ Contravariant = Contravariant
  v             \/ Omnivariant   = v
  Omnivariant   \/ v             = v
  _             \/ _             = Invariant

  Covariant     /\ Covariant     = Covariant
  Contravariant /\ Contravariant = Contravariant
  v             /\ Invariant     = v
  Invariant     /\ v             = v
  _             /\ _             = Omnivariant

-- | The qualifier lattice
-- @
--  Qa
--  |
--  Qu
-- @
instance PO Q where
  Qu \/ Qu = Qu
  _  \/ _  = Qa
  Qa /\ Qa = Qa
  _  /\ _  = Qu

instance Ord Q where
  (<=) = (<:)

-- | The 'QualSet' partial order
-- (relation only defined for same-length qualsets)
instance PO QualSet where
  QualSet q ixs /\? QualSet q' ixs'
    | q == q' = return (QualSet q (ixs `intersect` ixs'))
  qs /\? qs'  = fail $
      "GLB " ++ show qs ++ " /\\ " ++ show qs' ++ " does not exist"
  QualSet q ixs \/ QualSet q' ixs'
    | q == maxBound  = QualSet maxBound []
    | q' == maxBound = QualSet maxBound []
    | otherwise      = QualSet (q \/ q') (ixs `union` ixs')

-- | Variance has a bit more structure still -- it does sign analysis:
instance Num Variance where
  Covariant     * Covariant     = Covariant
  Covariant     * Contravariant = Contravariant
  Contravariant * Covariant     = Contravariant
  Contravariant * Contravariant = Covariant
  Omnivariant   * _             = Omnivariant
  _             * Omnivariant   = Omnivariant
  _             * _             = Invariant

  (+) = (\/)
  negate        = (* Contravariant)
  abs x         = x * x
  signum        = id

  x - y         = x + negate y

  fromInteger n | n > 0     = Covariant
                | n < 0     = Contravariant
                | otherwise = Omnivariant

