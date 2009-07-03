{-# LANGUAGE
      EmptyDataDecls,
      FlexibleContexts,
      FlexibleInstances,
      GADTs,
      ImpredicativeTypes,
      ParallelListComp,
      RankNTypes,
      TypeFamilies #-}
module Syntax (
  Language(..), A, C, LangRep(..),
  Q(..), Var(..), TyVar(..),

  TyDen(..), Variance(..),
  Type(..), TypeI, TEnv,
  Prog(..), ProgI,
  Decl(..), DeclI,
  Mod(..), ModI, TyDec(..), TyDecI,

  Expr(), ExprI, Expr'(..), Binding(..), BindingI, fv, expr',
  exCon, exStr, exInt, exIf, exCase, exLet, exLetRec,
  exVar, exPair, exLetPair,
  exAbs, exApp, exTAbs, exTApp, exSeq, exCast,

  PO(..),

  tdUnit, tdBool, tdInt, tdString, tdEither, tdTuple, tdArr, tdLol,

  dualSessionType,
  tdDual, tdSend, tdRecv, tdSelect, tdFollow,

  tyGround, tyArr, tyLol, tyTuple,
  tyUnitI, tyArrI, tyLolI, tyTupleI,

  ftv, freshTyVar, freshTyVars, tysubst, qualifier, tystrip,
  funtypes,
  ctype2atype, atype2ctype, cgetas, agetcs,

  syntacticValue, constants, modName, prog2decls,
  unfoldExAbs, unfoldTyAll, unfoldExTApp, unfoldExApp, unfoldTyFun
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
  deriving Eq

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
data TyDen =
  TdAbs {
    tdId    :: Integer,
    tdArity :: [Variance], -- The variance of each of its parameters
    tdQual  :: [Either Int Q],
                           -- The qualifier of the type is the lub of
                           -- the qualifiers of the named parameters and
                           -- possibly some constants
    tdTrans :: Bool
  }

data Type i w where
  TyCon { tycon  :: String,
          tyargs :: [Type i w],
          tyinfo :: i } :: Type i w
  TyVar :: TyVar -> Type i w
  TyAll :: TyVar -> Type i w -> Type i w
  TyMu  :: TyVar -> Type i w -> Type i w
  TyC   :: Type i C -> Type i A
  TyA   :: Type i A -> Type i C

type TEnv w = Env Var (TypeI w)

data Prog i = Prog [Decl i] (Expr i C)

data Decl i = DcMod (Mod i)
            | DcTyp (TyDec i)

data Mod i  = MdA Var (Maybe (Type i A)) (Expr i A)
            | MdC Var (Maybe (Type i C)) (Expr i C)
            | MdInt Var (Type i A) Var

data TyDec i = TdAbsC {
                 tdName      :: String,
                 tdParams    :: [TyVar]
               }
             | TdAbsA {
                 tdName      :: String,
                 tdParams    :: [TyVar],
                 tdVariances :: [Variance],
                 tdaQual     :: [Either TyVar Q]
               }
             | TdSynC {
                 tdName      :: String,
                 tdParams    :: [TyVar],
                 tdcRHS      :: Type () C
             }
             | TdSynA {
                 tdName      :: String,
                 tdParams    :: [TyVar],
                 tdaRHS      :: Type () A
             }

data Expr i w = Expr { fv_ :: FV, expr'_ :: Expr' i w }
type FV     = M.Map Var Integer
data Expr' i w = ExCon String
               | ExStr String
               | ExInt Integer
               | ExIf (Expr i w) (Expr i w) (Expr i w)
               | ExCase (Expr i w) (Var, Expr i w) (Var, Expr i w)
               | ExLet Var (Expr i w) (Expr i w)
               | ExLetRec [Binding i w] (Expr i w)
               | ExVar Var
               | ExPair (Expr i w) (Expr i w)
               | ExLetPair (Var, Var) (Expr i w) (Expr i w)
               | ExAbs Var (Type i w) (Expr i w)
               | ExApp (Expr i w) (Expr i w)
               | ExTAbs TyVar (Expr i w)
               | ExTApp (Expr i w) (Type i w)
               | ExSeq (Expr i w) (Expr i w)
               | ExCast (Expr i w) (Type i w) (Type i A)

data Binding i w = Binding {
  bnvar  :: Var,
  bntype :: Type i w,
  bnexpr :: Expr i w
}

type ExprI    = Expr TyDen
type TypeI    = Type TyDen
type DeclI    = Decl TyDen
type ModI     = Mod TyDen
type TyDecI   = TyDec TyDen
type BindingI = Binding TyDen
type ProgI    = Prog TyDen

fv :: Expr i w -> FV
fv  = fv_

expr' :: Expr i w -> Expr' i w
expr'  = expr'_

exCon :: String -> Expr i w
exCon  = Expr M.empty . ExCon

exStr :: String -> Expr i w
exStr  = Expr M.empty . ExStr

exInt :: Integer -> Expr i w
exInt  = Expr M.empty . ExInt

exIf  :: Expr i w -> Expr i w -> Expr i w -> Expr i w
exIf ec et ef = Expr {
  fv_    = fv ec |*| (fv et |+| fv ef),
  expr'_ = ExIf ec et ef
}

exCase  :: Expr i w -> (Var, Expr i w) -> (Var, Expr i w) -> Expr i w
exCase e (xl, el) (xr, er) = Expr {
  fv_    = fv e |*| ((fv el |-| xl) |+| (fv er |-| xr)),
  expr'_ = ExCase e (xl, el) (xr, er)
}

exLet :: Var -> Expr i w -> Expr i w -> Expr i w
exLet x e1 e2 = Expr {
  fv_    = fv e1 |*| (fv e2 |-| x),
  expr'_ = ExLet x e1 e2
}

exLetRec :: [Binding i w] -> Expr i w -> Expr i w
exLetRec bs e2 = Expr {
  fv_    = let es  = map bnexpr bs
               vs  = map bnvar  bs
               pot = foldr (|*|) (fv e2) (map fv es)
           in foldl (|-|) pot vs,
  expr'_ = ExLetRec bs e2
}

exVar :: Var -> Expr i w
exVar x = Expr {
  fv_    = M.singleton x 1,
  expr'_ = ExVar x
}

exPair :: Expr i w -> Expr i w -> Expr i w
exPair e1 e2 = Expr {
  fv_    = fv e1 |*| fv e2,
  expr'_ = ExPair e1 e2
}

exLetPair :: (Var, Var) -> Expr i w -> Expr i w -> Expr i w
exLetPair (x, y) e1 e2 = Expr {
  fv_    = fv e1 |*| ((fv e2 |-| x) |-| y),
  expr'_ = ExLetPair (x, y) e1 e2
}

exAbs :: Var -> Type i w -> Expr i w -> Expr i w
exAbs x t e = Expr {
  fv_    = fv e |-| x,
  expr'_ = ExAbs x t e
}

exApp :: Expr i w -> Expr i w -> Expr i w
exApp e1 e2 = Expr {
  fv_    = fv e1 |*| fv e2,
  expr'_ = ExApp e1 e2
}

exTAbs :: TyVar -> Expr i w -> Expr i w
exTAbs tv e = Expr {
  fv_    = fv e,
  expr'_ = ExTAbs tv e
}

exTApp :: Expr i w -> Type i w -> Expr i w
exTApp e1 t2 = Expr {
  fv_    = fv e1,
  expr'_ = ExTApp e1 t2
}

exSeq :: Expr i w -> Expr i w -> Expr i w
exSeq e1 e2 = Expr {
  fv_    = fv e1 |*| fv e2,
  expr'_ = ExSeq e1 e2
}

exCast :: Expr i w -> Type i w -> Type i A -> Expr i w
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

instance Eq TyDen where
  td == td' = tdId td == tdId td'

instance Language w => Eq (Type TyDen w) where
  TyCon _ [p] td == t | td == tdDual = dualSessionType p == t
  t == TyCon _ [p] td | td == tdDual = t == dualSessionType p
  TyCon _ ps td == TyCon _ ps' td' =
    td == td' && all2 (==) ps ps'
  TyA t        == TyA t'          = t == t'
  TyC t        == TyC t'          = t == t'
  TyVar x      == TyVar x'        = x == x'
  TyAll x t    == TyAll x' t'     =
    tvqual x == tvqual x' && t == tysubst x' (TyVar x `asTypeOf` t') t'
  TyMu x t     == TyMu x' t'      =
    tvqual x == tvqual x' && t == tysubst x' (TyVar x `asTypeOf` t') t'
  TyA (TyC t)  == t'              = t == t'
  TyC (TyA t)  == t'              = t == t'
  t            == TyA (TyC t')    = t == t'
  t            == TyC (TyA t')    = t == t'
  _            == _               = False

instance Show Q where
  showsPrec _ Qa = ('A':)
  showsPrec _ Qu = ('U':)

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
--  * (\/), (/\)    (only if it's a lattice)
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

instance Language w => PO (Type TyDen w) where
  -- Special cases for dual session types:
  ifMJ b (TyCon _ [p] td) t | td == tdDual = ifMJ b (dualSessionType p) t
  ifMJ b t (TyCon _ [p] td) | td == tdDual = ifMJ b t (dualSessionType p)
  -- Special cases for ->/-o subtyping:
  ifMJ b (TyCon _ ps td) (TyCon _ ps' td')
    | td == tdArr && td' == tdLol || td == tdLol && td' == tdArr
      = ifMJ b (build ps) (build ps')
    where build ps0 = if b
                        then TyCon "-o" ps0 tdLol
                        else TyCon "->" ps0 tdArr
  -- Otherwise:
  ifMJ b (TyCon tc ps td) (TyCon _ ps' td') =
    if td == td' then do
      params <- sequence
        [ case var of
            Covariant     -> ifMJ b p p'
            Contravariant -> ifMJ (not b) p p'
            Invariant     -> if p == p'
                             then return p
                             else fail "\\/? or /\\?: Does not exist"
            Omnivariant   -> fail "\\/? or /\\?: It's a mystery"
           | var <- tdArity td
           | p   <- ps
           | p'  <- ps' ]
      return (TyCon tc params td)
    else fail "\\/? or /\\?: Does not exist"
  ifMJ b (TyAll a t)   (TyAll a' t')  = ifMJBind TyAll b (a, t) (a', t')
  ifMJ b (TyMu a t)    (TyMu a' t')   = ifMJBind TyMu  b (a, t) (a', t')
  ifMJ b (TyC (TyA t)) t'             = ifMJ b t t'
  ifMJ b (TyA (TyC t)) t'             = ifMJ b t t'
  ifMJ b t             (TyC (TyA t')) = ifMJ b t t'
  ifMJ b t             (TyA (TyC t')) = ifMJ b t t'
  ifMJ _ t t' =
    if t == t'
      then return t
      else fail "\\/? or /\\?: Does not exist"

ifMJBind :: (Monad m, Language w) =>
            (TyVar -> TypeI w -> TypeI w) -> Bool ->
            (TyVar, TypeI w) -> (TyVar, TypeI w) ->
            m (TypeI w)
ifMJBind cons b (a, t) (a', t') = do
  qual <- ifMJ (not b) (tvqual a) (tvqual a')
  if qual == tvqual a
    then do
      tt' <- ifMJ b t (tysubst a' (TyVar a `asTypeOf` t') t')
      return (cons a tt')
    else do
      t't <- ifMJ b (tysubst a (TyVar a' `asTypeOf` t) t) t'
      return (cons a' t't)

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
  type OtherLang w
  reifyLang   :: LangRep w
  langCase    :: f w -> (w ~ C => f C -> r) -> (w ~ A => f A -> r) -> r
  langMapType :: Functor f =>
                 (forall w'. Language w' => f (Type td w')) -> f (Type td w)

instance Language C where
  type OtherLang C = A
  reifyLang        = C
  langCase x fc _  = fc x
  langMapType x    = fmap TyA x

instance Language A where
  type OtherLang A = C
  reifyLang        = A
  langCase x _ fa  = fa x
  langMapType x    = fmap TyC x

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

ftv :: TypeI w -> M.Map TyVar Variance
ftv (TyCon _ ts td)= M.unionsWith (+)
                       [ M.map (* var) m
                       | var <- tdArity td
                       | m   <- map ftv ts ]
ftv (TyVar tv)     = M.singleton tv 1
ftv (TyAll tv t)   = M.delete tv (ftv t)
ftv (TyMu tv t)    = M.delete tv (ftv t)
ftv (TyC t)        = M.map (const Invariant)
                           (M.unions (map ftv (cgetas t)))
ftv (TyA t)        = M.map (const Invariant)
                           (M.unions (map ftv (agetcs t)))

freshTyVars :: [TyVar] -> M.Map TyVar a -> [TyVar]
freshTyVars tvs0 m0 = loop tvs0 m1 where
  m1 = M.union (M.map (const ()) m0)
               (M.fromList [ (tv, ()) | tv <- tvs0 ])
  loop (tv:tvs) m' = let tv' = freshTyVar tv m'
                      in tv' : loop tvs (M.insert tv' () m')
  loop _        _ = []

freshTyVar :: TyVar -> M.Map TyVar a -> TyVar
freshTyVar tv m = if tv `M.member` m
                    then loop 0
                    else tv
  where
    attach n = tv { tvname = Var (unVar (tvname tv) ++ show n) }
    loop    :: Int -> TyVar
    loop n   =
      let tv' = attach n
      in if tv' `M.member` m
           then loop (n + 1)
           else tv'

tysubst :: (Language w, Language w') =>
           TyVar -> TypeI w' -> TypeI w -> TypeI w
tysubst a t = ts where
  ts :: Language w => TypeI w -> TypeI w
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
                        else
                          let a'' = freshTyVar a' (ftv t)
                              t'' = TyVar a'' `asTypeOf` t'
                          in TyAll a'' (ts (tysubst a' t'' t')))
                    (TyAll a' (ts t'))
  ts (TyMu a' t')
                = sameLang t' t
                    (\_ _ ->
                      if a' == a
                        then TyMu a' t'
                        else
                          let a'' = freshTyVar a' (ftv t)
                              t'' = TyVar a'' `asTypeOf` t'
                          in TyMu a'' (ts (tysubst a' t'' t')))
                    (TyMu a' (ts t'))
  ts (TyCon c tys td)
                = TyCon c (map ts tys) td
  ts (TyA t')
                = TyA (ts t')
  ts (TyC t')
                = TyC (ts t')

-- Helper for finding the dual of a session type (since we can't
-- express this direction in the type system)
dualSessionType :: TypeI w -> TypeI w
dualSessionType  = d where
  d (TyCon "->" [TyCon "send" [ta] _, tr] _)
    = TyCon "->" [TyCon "recv" [ta] tdRecv, d tr] tdArr
  d (TyCon "->" [TyCon "recv" [ta] _, tr] _)
    = TyCon "->" [TyCon "send" [ta] tdSend, d tr] tdArr
  d (TyCon "select" [TyCon "*" [t1, t2] _] _)
    = TyCon "follow" [TyCon "*" [d t1, d t2] tdTuple] tdFollow
  d (TyCon "follow" [TyCon "*" [t1, t2] _] _)
    = TyCon "select" [TyCon "*" [d t1, d t2] tdTuple] tdSelect
  d (TyMu tv t)
    = TyMu tv (d t)
  d t = t

tdUnit, tdBool, tdInt, tdString,
  tdArr, tdLol, tdTuple, tdEither :: TyDen

tdUnit       = TdAbs (-1)  []          []                True
tdBool       = TdAbs (-2)  []          []                True
tdInt        = TdAbs (-3)  []          []                True
tdString     = TdAbs (-4)  []          []                True
tdArr        = TdAbs (-5)  [-1, 1]     []                False
tdLol        = TdAbs (-6)  [-1, 1]     [Right Qa]        False
tdTuple      = TdAbs (-7)  [1, 1]      [Left 0, Left 1]  False
tdEither     = TdAbs (-8)  [1, 1]      [Left 0, Left 1]  False

tdDual, tdSend, tdRecv, tdSelect, tdFollow :: TyDen
-- For session types:
tdDual       = TdAbs (-11) [-1] []                False
tdSend       = TdAbs (-12) [1]  []                False
tdRecv       = TdAbs (-13) [-1] []                False
tdSelect     = TdAbs (-14) [1]  []                False
tdFollow     = TdAbs (-15) [1]  []                False

tyGround      :: String -> Type () w
tyGround s     = TyCon s [] ()

tyArr         :: Type () w -> Type () w -> Type () w
tyArr a b      = TyCon "->" [a, b] ()

tyLol         :: Type () w -> Type () w -> Type () w
tyLol a b      = TyCon "-o" [a, b] ()

tyTuple       :: Type () w -> Type () w -> Type () w
tyTuple a b    = TyCon "*" [a, b] ()

tyUnitI        :: TypeI C
tyUnitI         = TyCon "unit" [] tdUnit

tyArrI         :: TypeI w -> TypeI w -> TypeI w
tyArrI a b      = TyCon "->" [a, b] tdArr

tyLolI         :: TypeI w -> TypeI w -> TypeI w
tyLolI a b      = TyCon "-o" [a, b] tdLol

tyTupleI       :: TypeI w -> TypeI w -> TypeI w
tyTupleI a b    = TyCon "*" [a, b] tdTuple

qualifier     :: TypeI A -> Q
qualifier (TyCon _ ps td) = foldl max minBound qs' where
  qs = map qualifier ps
  toQ (Left ix) = qs !! ix
  toQ (Right q) = q
  qs' = map toQ (tdQual td)
qualifier (TyVar (TV _ q))   = q
qualifier (TyAll _ t)        = qualifier t
qualifier (TyMu _ t)         = qualifier t
qualifier _                  = Qu

tystrip :: Type i w -> Type () w
tystrip (TyCon n ts _) = TyCon n (map tystrip ts) ()
tystrip (TyVar x)      = TyVar x
tystrip (TyAll xs ts)  = TyAll xs (tystrip ts)
tystrip (TyMu xs ts)   = TyMu xs (tystrip ts)
tystrip (TyA t)        = TyA (tystrip t)
tystrip (TyC t)        = TyC (tystrip t)

-- Funtional types
funtypes    :: [TyDen]
funtypes     = [tdArr, tdLol]

cgetas :: Type i C -> [Type i A]
cgetas (TyCon _ ts _) = concatMap cgetas ts
cgetas (TyVar _)      = []
cgetas (TyAll _ t)    = cgetas t
cgetas (TyMu _ t)     = cgetas t
cgetas (TyA t)        = [t]
cgetas _              = [] -- can't happen

agetcs :: Type i A -> [Type i C]
agetcs (TyCon _ ts _) = concatMap agetcs ts
agetcs (TyVar _)      = []
agetcs (TyAll _ t)    = agetcs t
agetcs (TyMu _ t)     = agetcs t
agetcs (TyC t)        = [t]
agetcs _              = [] -- can't happen

ctype2atype :: TypeI C -> TypeI A
ctype2atype (TyCon n ps td) | tdTrans td
  = TyCon n (map ctype2atype ps) td
ctype2atype (TyCon _ [td, tr] d) | d == tdArr
  = TyCon "->" [ctype2atype td, ctype2atype tr] tdArr
ctype2atype (TyAll tv t)
                      = TyAll tv (ctype2atype t')
                        where t'  = tysubst tv (TyA (TyVar tv)) t
ctype2atype (TyMu tv t)
                      = TyMu tv (ctype2atype t')
                        where t'  = tysubst tv (TyA (TyVar tv)) t
ctype2atype (TyA t)   = t
ctype2atype t         = TyC t

atype2ctype :: TypeI A -> TypeI C
atype2ctype (TyCon n ps td) | tdTrans td
  = TyCon n (map atype2ctype ps) td
atype2ctype (TyCon _ [td, tr] d) | d `elem` funtypes
  = TyCon "->" [atype2ctype td, atype2ctype tr] tdArr
atype2ctype (TyAll tv t) | tvqual tv == Qu
                      = TyAll tv (atype2ctype t')
                        where t' = tysubst tv (TyC (TyVar tv)) t
atype2ctype (TyMu tv t) | tvqual tv == Qu
                      = TyMu tv (atype2ctype t')
                        where t' = tysubst tv (TyC (TyVar tv)) t
atype2ctype (TyC t)   = t
atype2ctype t         = TyA t

syntacticValue :: Expr i w -> Bool
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
constants  = [ "()", "unroll" ]

modName :: Mod i -> Var
modName (MdA x _ _)   = x
modName (MdC x _ _)   = x
modName (MdInt x _ _) = x

prog2decls :: Prog i -> [Decl i]
prog2decls (Prog ds e) = ds ++ [DcMod (MdC (Var "it") Nothing e)]

-- Unfolding various sequences

unfoldExAbs :: Expr i w -> ([Either (Var, Type i w) TyVar], Expr i w)
unfoldExAbs  = unscanr each where
  each e = case expr' e of
    ExAbs x t e' -> Just (Left (x, t), e')
    ExTAbs tv e' -> Just (Right tv, e')
    _            -> Nothing

unfoldTyAll :: Type i w -> ([TyVar], Type i w)
unfoldTyAll  = unscanr each where
  each (TyAll x t) = Just (x, t)
  each _           = Nothing

unfoldExTApp :: Expr i w -> ([Type i w], Expr i w)
unfoldExTApp  = unscanl each where
  each e = case expr' e of
    ExTApp e' t  -> Just (t, e')
    _            -> Nothing

unfoldExApp :: Expr i w -> ([Expr i w], Expr i w)
unfoldExApp  = unscanl each where
  each e = case expr' e of
    ExApp e1 e2 -> Just (e2, e1)
    _           -> Nothing

unfoldTyFun :: TypeI w -> ([TypeI w], TypeI w)
unfoldTyFun  = unscanr each where
  each (TyCon _ [ta, tr] td) | td `elem` funtypes = Just (ta, tr)
  each _                                         = Nothing

