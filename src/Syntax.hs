{-# LANGUAGE
      EmptyDataDecls,
      FlexibleContexts,
      GADTs,
      ImpredicativeTypes,
      ParallelListComp,
      RankNTypes,
      TypeFamilies #-}
module Syntax (
  Language(..), A, C, LangRep(..),
  Q(..), Var(..), TyVar(..),

  TyInfo(..), Variance(..),
  Type(..), TEnv,
  Prog(..), Mod(..),

  Expr(), Expr'(..), fv, expr',
  exCon, exStr, exInt, exIf, exLet, exVar, exPair, exLetPair,
  exAbs, exApp, exTAbs, exTApp, exSeq, exCast,

  PO(..),

  tyNothing, tyArr, tyLol, tyPair, tyGround,
  tysubst, tienv, tcinfo, qualifier,
  transparent, funtypes,
  ctype2atype, atype2ctype, cgetas, agetcs,

  syntacticValue, constants, modName,
  unfoldExAbs, unfoldTyAll, unfoldExTApp
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

-- Type variables
data TyVar = TV { tvname :: Var, tvqual :: Q }
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
  TyCon { tycon :: String,
          tyargs :: [Type w] } :: Type w
  TyVar :: TyVar -> Type w
  TyAll :: TyVar -> Type w -> Type w
  TyC   :: Type C -> Type A
  TyA   :: Type A -> Type C

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
             | ExTAbs TyVar (Expr w)
             | ExTApp (Expr w) (Type w)
             | ExSeq (Expr w) (Expr w)
             | ExCast (Expr w) (Type w) (Type A)

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

exTAbs :: TyVar -> Expr w -> Expr w
exTAbs tv e = Expr {
  fv_    = fv e,
  expr'_ = ExTAbs tv e
}

exTApp :: Expr w -> Type w -> Expr w
exTApp e1 t2 = Expr {
  fv_    = fv e1,
  expr'_ = ExTApp e1 t2
}

exSeq :: Expr w -> Expr w -> Expr w
exSeq e1 e2 = Expr {
  fv_    = fv e1 |*| fv e2,
  expr'_ = ExSeq e1 e2
}

exCast :: Expr w -> Type w -> Type A -> Expr w
exCast e t1 t2 = Expr {
  fv_    = fv e,
  expr'_ = ExCast e t1 t2
}

(|*|), (|+|) :: FV -> FV -> FV
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: FV -> Var -> FV
(|-|)  = flip M.delete

-----
----- Some classes and instances
-----

instance Language w => Eq (Type w) where
  TyCon c ps == TyCon c' ps' = c == c' && all2 (==) ps ps'
  TyA t      == TyA t'       = t == t'
  TyC t      == TyC t'       = t == t'
  TyVar x    == TyVar x'     = x == x'
  TyAll x t  == TyAll x' t'  = tvqual x == tvqual x' &&
                               t == tysubst x' (TyVar x `asTypeOf` t') t'
  _          == _            = False

instance Show Variance where
  showsPrec _ Invariant     = ('1':)
  showsPrec _ Covariant     = ('+':)
  showsPrec _ Contravariant = ('-':)
  showsPrec _ Omnivariant   = ('0':)

instance Show Var where
  show = unVar

instance Show TyVar where
  show (TV x Qu) = "'" ++ show x
  show (TV x Qa) = "'<" ++ show x

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

instance Language w => PO (Type w) where
  -- Special cases for ->/-o subtyping:
  ifMJ True  (TyCon "->" ps) (TyCon "-o" ps')
      = ifMJ True (TyCon "-o" ps) (TyCon "-o" ps')
  ifMJ True  (TyCon "-o" ps) (TyCon "->" ps')
      = ifMJ True (TyCon "-o" ps) (TyCon "-o" ps')
  ifMJ False (TyCon "->" ps) (TyCon "-o" ps')
      = ifMJ True (TyCon "->" ps) (TyCon "->" ps')
  ifMJ False (TyCon "-o" ps) (TyCon "->" ps')
      = ifMJ True (TyCon "->" ps) (TyCon "->" ps')
  -- Otherwise:
  ifMJ b (TyCon tc ps) (TyCon tc' ps') =
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
      return (TyCon tc params)
    else fail "\\/? or /\\?: Does not exist"
  ifMJ b (TyAll a t) (TyAll a' t') = do
    qual <- ifMJ (not b) (tvqual a) (tvqual a')
    if qual == tvqual a
      then do
        tt' <- ifMJ b t (tysubst a' (TyVar a `asTypeOf` t') t')
        return (TyAll a tt')
      else do
        t't <- ifMJ b (tysubst a (TyVar a' `asTypeOf` t) t) t'
        return (TyAll a' t't)
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
  langCase    :: f w -> (w ~ C => f C -> r) -> (w ~ A => f A -> r) -> r
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

sameLang :: (Language w, Language w') =>
            f w -> g w' -> (w ~ w' => f w -> g w -> r) -> r -> r
sameLang x y same diff =
  langCase x
    (\xc -> langCase y
      (\yc -> same xc yc)
      (\_  -> diff))
    (\xa -> langCase y
      (\_  -> diff)
      (\ya -> same xa ya))

---
--- Syntax Utils
---

tysubst :: (Language w, Language w') =>
           TyVar -> Type w' -> Type w -> Type w
tysubst a t = ts where
  ts :: Language w => Type w -> Type w
  ts t'@(TyVar a')
                = sameLang t' t
                    (\_ t0 ->
                      if a' == a
                        then t0
                        else TyVar a')
                    (TyVar a')
  ts (TyAll a' t')
                = sameLang t' t
                    (\_ _ ->
                      if a' == a
                        then TyAll a' t'
                        else TyAll a' (ts t'))
                    (TyAll a' (ts t'))
  ts (TyCon c tys)
                = TyCon c (map (ts) tys)
  ts (TyA t')
                = TyA (ts t')
  ts (TyC t')
                = TyC (ts t')

tienv         :: Env String TyInfo
tienv          = fromList [
                   ("*",        pair),
                   ("->",       arr),
                   ("-o",       lol),
                   ("ref",      ref),
                   ("thread",   thread),
                   ("future",   future),
                   ("cofuture", cofuture)
                ]
  where
  arr      = TyInfo [-1, 1] (const Qu)
  lol      = TyInfo [-1, 1] (const Qa)
  ref      = TyInfo [Invariant] (const Qa)
  pair     = TyInfo [1, 1] (\[q1, q2] -> q1 \/ q2)
  thread   = TyInfo [] (const Qa)
  future   = TyInfo [1] (const Qa)
  cofuture = TyInfo [-1] (const Qa)

tiNothing :: TyInfo
tiNothing = TyInfo (repeat Invariant) (const Qu)

tcinfo :: String -> TyInfo
tcinfo s = case tienv =.= s of
  Just ti -> ti
  Nothing -> tiNothing

tyGround :: String -> Type w
tyGround s = TyCon s []

tyArr         :: Type w -> Type w -> Type w
tyArr a b      = TyCon "->" [a, b]

tyLol         :: Type w -> Type w -> Type w
tyLol a b      = TyCon "-o" [a, b]

tyPair        :: Type w -> Type w -> Type w
tyPair a b     = TyCon "*" [a, b]

tyNothing     :: Type w
tyNothing      = TyCon "" []

qualifier     :: Type A -> Q
qualifier (TyCon tc ps)      = tiQual (tcinfo tc) (map qualifier ps)
qualifier (TyVar (TV _ q) )  = q
qualifier (TyAll _ t)        = qualifier t
qualifier _                  = Qu

-- Types that pass transparently through boundaries
transparent :: [String]
transparent  = ["string", "int", "bool", "unit"]

-- Funtional types
funtypes    :: [String]
funtypes     = ["->", "-o"]

cgetas :: Type C -> [Type A]
cgetas (TyCon _ ts) = concatMap cgetas ts
cgetas (TyVar _)    = []
cgetas (TyAll _ t)  = cgetas t
cgetas (TyA t)      = [t]
cgetas _            = [] -- can't happen

agetcs :: Type A -> [Type C]
agetcs (TyCon _ ts) = concatMap agetcs ts
agetcs (TyVar _)    = []
agetcs (TyAll _ t)  = agetcs t
agetcs (TyC t)      = [t]
agetcs _            = [] -- can't happen

ctype2atype :: Type C -> Type A
ctype2atype (TyCon n ps) | n `elem` transparent
  = TyCon n (map ctype2atype ps)
ctype2atype (TyCon "->" [td, tr])
  = tyArr (ctype2atype td) (ctype2atype tr)
ctype2atype (TyAll tv t)
                      = TyAll tv (ctype2atype t')
                        where t'  = tysubst tv (TyA (TyVar tv)) t
ctype2atype (TyA t)   = t
ctype2atype t         = TyC t

atype2ctype :: Type A -> Type C
atype2ctype (TyCon n ps) | n `elem` transparent
  = TyCon n (map atype2ctype ps)
atype2ctype (TyCon n [td, tr]) | n `elem` funtypes
  = tyArr (atype2ctype td) (atype2ctype tr)
atype2ctype (TyAll tv t) | tvqual tv == Qu
                      = TyAll tv (atype2ctype t')
                        where t' = tysubst tv (TyC (TyVar tv)) t
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
  ExTAbs _ _   -> True
  ExTApp e1 _  -> syntacticValue e1
  _            -> False

constants :: [String]
constants  = [ "()" ]

modName :: Mod -> Var
modName (MdA x _ _)   = x
modName (MdC x _ _)   = x
modName (MdInt x _ _) = x

-- Unfolding various sequences

unfoldExAbs :: Expr w -> ([Either (Var, Type w) TyVar], Expr w)
unfoldExAbs  = unscanr each where
  each e = case expr' e of
    ExAbs x t e' -> Just (Left (x, t), e')
    ExTAbs tv e' -> Just (Right tv, e')
    _            -> Nothing

unfoldTyAll :: Type w -> ([TyVar], Type w)
unfoldTyAll  = unscanr each where
  each (TyAll x t) = Just (x, t)
  each _           = Nothing

unfoldExTApp :: Expr w -> ([Type w], Expr w)
unfoldExTApp  = unscanl each where
  each e = case expr' e of
    ExTApp e' t  -> Just (t, e')
    _            -> Nothing
