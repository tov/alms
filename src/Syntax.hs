{-# LANGUAGE
      EmptyDataDecls,
      GADTs,
      ParallelListComp,
      RankNTypes #-}
module Syntax (
  Language(..), A, C, LangRep(..),
  Q(..), Var(..),

  TyInfo(..), Variance(..),
  Type(..), TEnv,
  Prog(..), Mod(..),

  Expr(), Expr'(..), fv, expr',
  exCon, exStr, exInt, exIf, exLet, exVar, exPair, exLetPair,
  exAbs, exApp, exSeq, exCast,

  PO(..),

  tyNothing, tyArr, tyLol, tyPair, tyGround,
  tienv, tcinfo, qualifier,
  transparent, funtypes, ctype2atype, atype2ctype,

  syntacticValue, constants, modName
) where

import Util
import Env

import qualified Data.Map as M

-- We have two languages:
data C
data A

data LangRep w where
  A :: LangRep A
  C :: LangRep C

-- Qualifiers
data Q = Qa | Qu
  deriving (Eq, Show)

-- Variables
data Var = Var { unVar :: String }
  deriving (Eq, Ord)

-- Variance
data Variance = Invariant
              | Covariant
              | Contravariant
              | Omnivariant
  deriving (Eq, Ord)

-- Info about a type constructor (for language A)
data TyInfo = TyInfo {
    tiArity :: [Variance], -- The variance of each of its parameters
    tiQual  :: [Q] -> Q    -- The qualifier of the type, given the
                           -- qualifiers of the parameters
  }

data Type w where
  TyApp { tycon :: String,
          tyargs :: [Type w] } :: Type w
  TyC  :: Type C -> Type A
  TyA  :: Type A -> Type C

type TEnv w = Env Var (Type w)

data Prog = Prog [Mod] (Expr C)

data Mod  = MdA Var (Type A) (Expr A)
          | MdC Var (Type C) (Expr C)
          | MdInt Var (Type A) Var

data Expr w = Expr { fv_ :: FV, expr'_ :: Expr' w }
type FV     = M.Map Var Integer
data Expr' w = ExCon String
             | ExStr String
             | ExInt Integer
             | ExIf (Expr w) (Expr w) (Expr w)
             | ExLet Var (Expr w) (Expr w)
             | ExVar Var
             | ExPair (Expr w) (Expr w)
             | ExLetPair (Var, Var) (Expr w) (Expr w)
             | ExAbs Var (Type w) (Expr w)
             | ExApp (Expr w) (Expr w)
             | ExSeq (Expr w) (Expr w)
             | ExCast (Expr w) (Type A)

fv :: Expr w -> FV
fv  = fv_

expr' :: Expr w -> Expr' w
expr'  = expr'_

exCon :: String -> Expr w
exCon  = Expr M.empty . ExCon

exStr :: String -> Expr w
exStr  = Expr M.empty . ExStr

exInt :: Integer -> Expr w
exInt  = Expr M.empty . ExInt

exIf  :: Expr w -> Expr w -> Expr w -> Expr w
exIf ec et ef = Expr {
  fv_    = fv ec |*| (fv et |+| fv ef),
  expr'_ = ExIf ec et ef
}

exLet :: Var -> Expr w -> Expr w -> Expr w
exLet x e1 e2 = Expr {
  fv_    = fv e1 |*| (fv e2 |-| x),
  expr'_ = ExLet x e1 e2
}

exVar :: Var -> Expr w
exVar x = Expr {
  fv_    = M.singleton x 1,
  expr'_ = ExVar x
}

exPair :: Expr w -> Expr w -> Expr w
exPair e1 e2 = Expr {
  fv_    = fv e1 |*| fv e2,
  expr'_ = ExPair e1 e2
}

exLetPair :: (Var, Var) -> Expr w -> Expr w -> Expr w
exLetPair (x, y) e1 e2 = Expr {
  fv_    = fv e1 |*| ((fv e2 |-| x) |-| y),
  expr'_ = ExLetPair (x, y) e1 e2
}

exAbs :: Var -> Type w -> Expr w -> Expr w
exAbs x t e = Expr {
  fv_    = fv e |-| x,
  expr'_ = ExAbs x t e
}

exApp :: Expr w -> Expr w -> Expr w
exApp e1 e2 = Expr {
  fv_    = fv e1 |*| fv e2,
  expr'_ = ExApp e1 e2
}

exSeq :: Expr w -> Expr w -> Expr w
exSeq e1 e2 = Expr {
  fv_    = fv e1 |*| fv e2,
  expr'_ = ExSeq e1 e2
}

exCast :: Expr w -> Type A -> Expr w
exCast e t = Expr {
  fv_    = fv e,
  expr'_ = ExCast e t
}

(|*|), (|+|) :: FV -> FV -> FV
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: FV -> Var -> FV
(|-|)  = flip M.delete

-----
----- Some classes and instances
-----

instance Eq (Type w) where
  TyApp c ps == TyApp c' ps' = c == c' && all2 (==) ps ps'
  TyA t      == TyA t'       = t == t'
  TyC t      == TyC t'       = t == t'
  _          == _            = False

instance Show Variance where
  showsPrec _ Invariant     = ('1':)
  showsPrec _ Covariant     = ('+':)
  showsPrec _ Contravariant = ('-':)
  showsPrec _ Omnivariant   = ('0':)

instance Show Var where
  show = unVar

instance Ord Q where
  (<=) = (<:)

instance Bounded Variance where
  minBound = Omnivariant
  maxBound = Invariant

instance Bounded Q where
  minBound = Qu
  maxBound = Qa

-- Minimal complete definition is one of:
--  * ifMJ
--  * (\/), (/\)
--  * (\/?), (/\?)
class Eq a => PO a where
  ifMJ :: Monad m => Bool -> a -> a -> m a
  ifMJ True  x y = return (x \/ y)
  ifMJ False x y = return (x /\ y)

  (\/?) :: Monad m => a -> a -> m a
  (\/?)  = ifMJ True

  (/\?) :: Monad m => a -> a -> m a
  (/\?)  = ifMJ False

  (\/)  :: a -> a -> a
  (/\)  :: a -> a -> a
  x \/ y = fromJust (x \/? y)
  x /\ y = fromJust (x /\? y)

  (<:)  :: a -> a -> Bool
  x <: y = Just x == (x /\? y)

infixl 7 /\, /\?
infixl 6 \/, \/?
infix 4 <:

--       (In)
--         T
--  (Co) +   - (Contra)
--         0
--      (Omni)
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

--  Qa
--  |
--  Qu
instance PO Q where
  Qu \/ Qu = Qu
  _  \/ _  = Qa
  Qa /\ Qa = Qa
  _  /\ _  = Qu

instance PO (Type w) where
  -- Special cases for ->/-o subtyping:
  ifMJ True  (TyApp "->" ps) (TyApp "-o" ps')
      = ifMJ True (TyApp "-o" ps) (TyApp "-o" ps')
  ifMJ True  (TyApp "-o" ps) (TyApp "->" ps')
      = ifMJ True (TyApp "-o" ps) (TyApp "-o" ps')
  ifMJ False (TyApp "->" ps) (TyApp "-o" ps')
      = ifMJ True (TyApp "->" ps) (TyApp "->" ps')
  ifMJ False (TyApp "-o" ps) (TyApp "->" ps')
      = ifMJ True (TyApp "->" ps) (TyApp "->" ps')
  -- Otherwise:
  ifMJ b (TyApp tc ps) (TyApp tc' ps') =
    if tc == tc' then do
      let ti = tcinfo tc
      params <- sequence
        [ case var of
            Covariant     -> ifMJ b p p'
            Contravariant -> ifMJ (not b) p p'
            Invariant     -> if p == p'
                             then return p
                             else fail "\\/? or /\\?: Does not exist"
            Omnivariant   -> fail "\\/? or /\\?: It's a mystery"
           | var <- tiArity ti
           | p   <- ps
           | p'  <- ps' ]
      return (TyApp tc params)
    else fail "\\/? or /\\?: Does not exist"
  ifMJ _ t t' =
    if t == t'
      then return t
      else fail "\\/? or /\\?: Does not exist"

-- Variance has a bit more structure still -- it does sign analysis:
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

-- In GHC 6.10, reifyLang is enough, but in 6.8, we need langCase
-- and langMapType, it seems.
class Language w where
  reifyLang   :: LangRep w
  langCase    :: f w -> (f C -> r) -> (f A -> r) -> r
  langMapType :: Functor f =>
                 (forall w'. Language w' => f (Type w')) -> f (Type w)

instance Language C where
  reifyLang       = C
  langCase x fc _ = fc x
  langMapType x   = fmap TyA x

instance Language A where
  reifyLang       = A
  langCase x _ fa = fa x
  langMapType x   = fmap TyC x

---
--- Syntax Utils
---

tienv         :: Env String TyInfo
tienv          = fromList [
                   ("*",      pair),
                   ("->",     arr),
                   ("-o",     lol),
                   ("ref",    ref),
                   ("thread", thread)
                ]
  where
  arr     = TyInfo [-1, 1] (const Qu)
  lol     = TyInfo [-1, 1] (const Qa)
  ref     = TyInfo [Invariant] (const Qa)
  pair    = TyInfo [1, 1] (\[q1, q2] -> q1 \/ q2)
  thread  = TyInfo [] (const Qa)

tiNothing :: TyInfo
tiNothing = TyInfo (repeat Invariant) (const Qu)

tcinfo :: String -> TyInfo
tcinfo s = case tienv =.= s of
  Just ti -> ti
  Nothing -> tiNothing

tyGround :: String -> Type w
tyGround s = TyApp s []

tyArr         :: Type w -> Type w -> Type w
tyArr a b      = TyApp "->" [a, b]

tyLol         :: Type w -> Type w -> Type w
tyLol a b      = TyApp "-o" [a, b]

tyPair        :: Type w -> Type w -> Type w
tyPair a b     = TyApp "*" [a, b]

tyNothing     :: Type w
tyNothing      = TyApp "" []

qualifier     :: Type A -> Q
qualifier (TyApp tc ps) = tiQual (tcinfo tc) (map qualifier ps)
qualifier _             = Qu

-- Types that pass transparently through boundaries
transparent :: [String]
transparent  = ["string", "int", "bool", "unit"]

-- Funtional types
funtypes    :: [String]
funtypes     = ["->", "-o"]

ctype2atype :: Type C -> Type A
ctype2atype (TyApp n ps) | n `elem` transparent
  = TyApp n (map ctype2atype ps)
ctype2atype (TyApp "->" [td, tr])
  = tyArr (ctype2atype td) (ctype2atype tr)
ctype2atype (TyA t)   = t
ctype2atype t         = TyC t

atype2ctype :: Type A -> Type C
atype2ctype (TyApp n ps) | n `elem` transparent
  = TyApp n (map atype2ctype ps)
atype2ctype (TyApp n [td, tr]) | n `elem` funtypes
  = tyArr (atype2ctype td) (atype2ctype tr)
atype2ctype (TyC t)   = t
atype2ctype t         = TyA t

syntacticValue :: Expr w -> Bool
syntacticValue e = case expr' e of
  ExCon _      -> True
  ExStr _      -> True
  ExInt _      -> True
  ExVar _      -> True
  ExPair e1 e2 -> syntacticValue e1 && syntacticValue e2
  ExAbs _ _ _  -> True
  _            -> False

constants :: [String]
constants  = [ "()", "ref", "swap" ]

modName :: Mod -> Var
modName (MdA x _ _)   = x
modName (MdC x _ _)   = x
modName (MdInt x _ _) = x

