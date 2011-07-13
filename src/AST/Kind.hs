{-# LANGUAGE
      DeriveDataTypeable,
      GeneralizedNewtypeDeriving,
      TemplateHaskell,
      TypeFamilies,
      TypeSynonymInstances,
      UnicodeSyntax #-}
module AST.Kind (
  -- * Qualifiers and variance
  QLit(..), Variance(..),
  -- ** Qualifier expressions
  QExp, QExp'(..), qeLit, qeVar, qeAnti, qeJoin,
  -- ** Qualifier operations
  (\-\), elimQLit, qLitSigil,
  -- ** Variance operations
  isQVariance,

  -- * Modules
) where

import Util
import Meta.DeriveNotable
import Data.Lattice
import AST.Anti
import AST.Notable
import {-# SOURCE #-} AST.Ident
import qualified Syntax.Strings as Strings

import Prelude ()
import Data.Generics (Typeable, Data)

---
--- QUALIFIERS, VARIANCES
---

{- | Usage qualifier literals

  A
  |
  U

-}
data QLit
  -- | unlimited
  = Qu
  -- | affine
  | Qa
  deriving (Eq, Ord, Bounded, Typeable, Data)

type QExp i = Located QExp' i

-- | Usage qualifier expressions
data QExp' i
  -- | qualifier literal
  = QeLit QLit
  -- | type variable
  | QeVar (TyVar i)
  -- | join
  | QeJoin (QExp i) (QExp i)
  -- | antiquote
  | QeAnti Anti
  deriving (Typeable, Data)

deriveNotable ''QExp

{- |
Type constructor variance forms a seven point lattice, which keeps track
of both polarity and parameters that should be treated as qualifiers.
In particular, given a unary type constructor T with variance +, T S <:
T U when S <: U; but if T has variance Q+, then T S <: T U when
|S| ≤ |U|, where |⋅| gives the qualifier of a type.

       =
      /|\
     / | \
    /  |  \
   +  Q=   -
   | /  \  |
   |/    \ |
  Q+      Q-
    \     /
     \   /
      \ /
       0

-}
data Variance
  -- | 0
  = Omnivariant
  -- | Q+
  | QCovariant
  -- | Q-
  | QContravariant
  -- | Q=
  | QInvariant
  -- | +
  | Covariant
  -- | -
  | Contravariant
  -- | =
  | Invariant
  deriving (Eq, Ord, Typeable, Data)

---
--- Order instances
---

instance Lattice QLit where
  Qa ⊔ _  = Qa
  Qu ⊔ ql = ql
  Qu ⊓ _  = Qu
  Qa ⊓ ql = ql
  Qa ⊑ Qu = False
  _  ⊑ _  = True

-- | Variances are a four point lattice with 'Invariant' on top and
--   'Omnivariant' on the bottom
instance Bounded Variance where
  minBound = Omnivariant
  maxBound = Invariant

instance Lattice Variance where
  Omnivariant    ⊔ v2             = v2
  v1             ⊔ Omnivariant    = v1
  QCovariant     ⊔ Covariant      = Covariant
  Covariant      ⊔ QCovariant     = Covariant
  QContravariant ⊔ Contravariant  = Contravariant
  Contravariant  ⊔ QContravariant = Contravariant
  v1             ⊔ v2
    | v1 == v2                    = v1
    | isQVariance v1 && isQVariance v2
                                  = QInvariant
    | otherwise                   = Invariant
  --
  Invariant      ⊓ v2             = v2
  v1             ⊓ Invariant      = v1
  QCovariant     ⊓ Covariant      = QCovariant
  Covariant      ⊓ QCovariant     = QCovariant
  QInvariant     ⊓ Covariant      = QCovariant
  Covariant      ⊓ QInvariant     = QCovariant
  QContravariant ⊓ Contravariant  = QContravariant
  Contravariant  ⊓ QContravariant = QContravariant
  QInvariant     ⊓ Contravariant  = QContravariant
  Contravariant  ⊓ QInvariant     = QContravariant
  QInvariant     ⊓ QCovariant     = QCovariant
  QCovariant     ⊓ QInvariant     = QCovariant
  QInvariant     ⊓ QContravariant = QContravariant
  QContravariant ⊓ QInvariant     = QContravariant
  v1             ⊓ v2
    | v1 == v2                    = v1
    | otherwise                   = Omnivariant
  --
  Omnivariant    ⊑ _              = True
  QCovariant     ⊑ Covariant      = True
  QContravariant ⊑ Contravariant  = True
  QCovariant     ⊑ QInvariant     = True
  QContravariant ⊑ QInvariant     = True
  _              ⊑ Invariant      = True
  v1             ⊑ v2             = v1 == v2

instance Bounded (QExp' i) where
  minBound = QeLit Qu
  maxBound = QeLit Qa

---
--- Other instances
---

instance Show QLit where
  showsPrec _ Qu = ('U':)
  showsPrec _ Qa = ('A':)

instance Show Variance where
  show Invariant      = Strings.invariant
  show Covariant      = Strings.covariant
  show Contravariant  = Strings.contravariant
  show Omnivariant    = Strings.omnivariant
  show QInvariant     = Strings.qinvariant
  show QCovariant     = Strings.qcovariant
  show QContravariant = Strings.qcontravariant

instance Monoid QLit where
  mempty  = minBound
  mappend = (⊔)

instance Monoid Variance where
  mempty  = minBound
  mappend = (⊔)

-- | Variances work like abstract sign arithmetic, where:
--    Omnivariant    = { 0 }
--    Covariant      = ℤ₊  = { 0, 1, 2, ... }
--    Contravariant  = ℤ₋  = { ..., -2, -1, 0 }
--    Invariant      = ℤ
--    QCovariant     = 2ℤ₊ = { 0, 2, 4, ... }
--    QContravariant = 2ℤ₋ = { ..., -4, -2, 0 }
--    QInvariant     = 2ℤ  = { ..., -4, -2, 0, 2, 4, ... }
--- In this view, addition gives the join for the variance lattice,
--  and multiplication gives the variance of composing type constructors
--  of the given variances (more or less).
instance Num Variance where
  (+) = (⊔)
  --
  Omnivariant    * _              = Omnivariant
  Covariant      * v2             = v2
  v1             * Covariant      = v1
  Contravariant  * v2             = negate v2
  v1             * Contravariant  = negate v1
  QCovariant     * v2             = v2 ⊓ QInvariant
  v1             * QCovariant     = v1 ⊓ QInvariant
  QContravariant * v2             = negate v2 ⊓ QInvariant
  v1             * QContravariant = negate v1 ⊓ QInvariant
  QInvariant     * _              = QInvariant
  _              * QInvariant     = QInvariant
  _              * _              = Invariant
  --
  abs Omnivariant               = Omnivariant
  abs v | isQVariance v         = QCovariant
        | otherwise             = Covariant
  --
  signum QCovariant             = Covariant
  signum QContravariant         = Contravariant
  signum QInvariant             = Invariant
  signum v                      = v
  --
  negate Covariant              = Contravariant
  negate Contravariant          = Covariant
  negate QCovariant             = QContravariant
  negate QContravariant         = QCovariant
  negate v                      = v
  --
  fromInteger i
    | i > 0     = if even i then QCovariant else Covariant
    | i < 0     = if even i then QContravariant else Contravariant
    | otherwise = Omnivariant

---
--- Operations
---

--
-- Qualifiers
--

-- | @a \-\ b@ is the least @c@ such that
--   @a ⊑ b ⊔ c@.  (This is sort of dual to a pseudocomplement.)
(\-\) ∷ QLit → QLit → QLit
Qa \-\ Qu = Qu
_  \-\ _  = Qu

elimQLit ∷ a → a → QLit → a
elimQLit u _ Qu = u
elimQLit _ a Qa = a

qLitSigil ∷ QLit → String
qLitSigil Qu = Strings.unlimited
qLitSigil Qa = Strings.affine

--
-- Variances
--

isQVariance ∷ Variance → Bool
isQVariance QCovariant     = True
isQVariance QContravariant = True
isQVariance QInvariant     = True
isQVariance _              = False

