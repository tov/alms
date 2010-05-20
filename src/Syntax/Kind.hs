{-# LANGUAGE
      DeriveDataTypeable,
      GeneralizedNewtypeDeriving,
      TemplateHaskell,
      TypeFamilies #-}
module Syntax.Kind (
  -- * Qualifiers, qualifiers sets, and variance
  QLit(..), QExp'(..),
  QExp, qeLit, qeVar, qeDisj, qeConj, qeAnti,
  QDen,
  Variance(..),
  -- ** Qualifier operations
  qConstBound, elimQLit,
  qDenToLit, qDenOfTyVar, qDenFtv,
  qInterpretM, qInterpret, qInterpretCanonical, qRepresent,
  qSubst,
  numberQDenM, numberQDen, numberQDenMap, denumberQDen
) where

import Meta.DeriveNotable
import PDNF (PDNF)
import qualified PDNF
import Syntax.Anti
import Syntax.Notable
import Syntax.POClass
import {-# SOURCE #-} Syntax.Ident
import Util

import Control.Monad.Identity (runIdentity)
import Data.List (elemIndex)
import Data.Generics (Typeable, Data)
import qualified Data.Map as M
import qualified Data.Set as S

-- QUALIFIERS, VARIANCES

-- | Usage qualifier literals
data QLit
  -- | affine
  = Qa
  -- | unlimited
  | Qu
  deriving (Eq, Typeable, Data)

-- | The syntactic version of qualifier expressions, which are
--   positive logical formulae over literals and type variables
data QExp' i
  = QeLit QLit
  | QeVar (TyVar i)
  | QeDisj [QExp i]
  | QeConj [QExp i]
  | QeAnti Anti
  deriving (Typeable, Data)

type QExp i = Located QExp' i

deriveNotable ['QeDisj, 'QeConj] ''QExp

-- | Synthetic constructor to avoid constructing nullary or unary
--   disjunctions
qeDisj :: [QExp i] -> QExp i
qeDisj []   = newN (QeLit Qu)
qeDisj [qe] = qe
qeDisj qes  = newN (QeDisj qes)

-- | Synthetic constructor to avoid constructing nullary or unary
--   conjunctions
qeConj :: [QExp i] -> QExp i
qeConj []   = newN (QeLit Qa)
qeConj [qe] = qe
qeConj qes  = newN (QeConj qes)

-- | The meaning of qualifier expressions
newtype QDen a = QDen { unQDen :: PDNF a }
  deriving (Eq, Ord, PO, Bounded, Typeable, Data, Show)

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

---
--- Operations
---

qConstBound :: Ord a => QDen a -> QLit
qConstBound (QDen qden) =
  if PDNF.isUnsat qden then Qu else Qa

elimQLit :: a -> a -> QLit -> a
elimQLit u _ Qu = u
elimQLit _ a Qa = a

-- | Find the meaning of a qualifier expression
qInterpretM :: (Monad m, Id i) => QExp i -> m (QDen (TyVar i))
qInterpretM (N note qe0) = case qe0 of
  QeLit Qu  -> return minBound
  QeLit Qa  -> return maxBound
  QeVar v   -> return (QDen (PDNF.variable v))
  QeDisj es -> bigVee `liftM` mapM qInterpretM es
  QeConj es -> bigWedge `liftM` mapM qInterpretM es
  QeAnti a  -> antifail ("Syntax.Kind.qInterpret: " ++ show (getLoc note)) a

-- | Find the meaning of a qualifier expression
qInterpret :: Id i => QExp i -> QDen (TyVar i)
qInterpret  = runIdentity . qInterpretM

-- | Convert a canonical representation back to a denotation.
--   (Unsafe if the representation is not actually canonical)
qInterpretCanonical :: Id i => QExp i -> QDen (TyVar i)
qInterpretCanonical (N _ (QeDisj clauses)) = QDen $
  PDNF.fromListsUnsafe $
    [ [ v ] | N _ (QeVar v) <- clauses ] ++
    [ [ v | N _ (QeVar v) <- clause ] | N _ (QeConj clause) <- clauses ]
qInterpretCanonical e = qInterpret e

-- | Return the canonical representation of the meaning of a
--   qualifier expression
qRepresent :: Id i => QDen (TyVar i) -> QExp i
qRepresent (QDen pdnf)
  | PDNF.isUnsat pdnf = newN (QeLit Qu)
  | PDNF.isValid pdnf = newN (QeLit Qa)
  | otherwise         =
      qeDisj (map (qeConj . map qeVar)
                  (PDNF.toLists pdnf))

qDenToLit :: Ord a => QDen a -> Maybe QLit
qDenToLit (QDen pdnf)
  | PDNF.isUnsat pdnf = Just Qu
  | PDNF.isValid pdnf = Just Qa
  | otherwise         = Nothing

qDenOfTyVar :: Ord a => a -> QDen a
qDenOfTyVar = QDen . PDNF.variable

qDenFtv :: Ord a => QDen a -> S.Set a
qDenFtv (QDen pdnf) = PDNF.support pdnf

qSubst :: Ord tv => tv -> QDen tv -> QDen tv -> QDen tv
qSubst v (QDen pdnf1) (QDen pdnf2) = QDen (PDNF.replace v pdnf1 pdnf2)

numberQDenM  :: (Ord tv, Monad m) =>
                (tv -> m (QDen Int)) ->
                [tv] -> QDen tv -> m (QDen Int)
numberQDenM unbound tvs (QDen pdnf) =
  liftM QDen $ PDNF.mapReplaceM pdnf $ \tv ->
    case tv `elemIndex` tvs of
      Nothing -> liftM unQDen $ unbound tv
      Just n  -> return (PDNF.variable n)

numberQDen  :: Ord tv => [tv] -> QDen tv -> QDen Int
numberQDen = runIdentity <$$> numberQDenM (const (return minBound))

numberQDenMap :: Ord tv =>
                 (tv -> QLit) ->
                 M.Map tv Int ->
                 QDen tv -> QDen Int
numberQDenMap lit m = runIdentity . numberQDenM get [] where
  get tv = case M.lookup tv m of
    Just i  -> return (QDen (PDNF.variable i))
    Nothing -> return (elimQLit minBound maxBound (lit tv))

-- | Given a qualifier set of indices into a list of qualifier
--   expressions, build the qualifier set over the qexps.
--   Assumes that the list is long enough for all indices.
denumberQDen :: Ord tv => [QDen tv] -> QDen Int -> QDen tv
denumberQDen qds (QDen pdnf) = QDen $
  PDNF.mapReplace pdnf $ \ix -> unQDen (qds !! ix)

instance Show QLit where
  showsPrec _ Qa = ('A':)
  showsPrec _ Qu = ('U':)

instance Show Variance where
  showsPrec _ Invariant     = ('=':)
  showsPrec _ Covariant     = ('+':)
  showsPrec _ Contravariant = ('-':)
  showsPrec _ Omnivariant   = ('*':)

instance Bounded QLit where
  minBound = Qu
  maxBound = Qa

instance Bounded (QExp' a) where
  minBound = QeLit minBound
  maxBound = QeLit maxBound

instance Bounded Variance where
  minBound = Omnivariant
  maxBound = Invariant

instance (Ord a, Num a) => Num (QDen a) where
  fromInteger = QDen . PDNF.variable . fromInteger
  (+)    = error "QDen.signum: not implemented"
  (*)    = error "QDen.signum: not implemented"
  abs    = error "QDen.signum: not implemented"
  signum = error "QDen.signum: not implemented"

-- | The variance lattice:
--
-- @
--       (In)
--         =
--  (Co) +   - (Contra)
--         *
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
instance PO QLit where
  Qu \/ Qu = Qu
  _  \/ _  = Qa
  Qa /\ Qa = Qa
  _  /\ _  = Qu

instance Ord QLit where
  (<=) = (<:)

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

