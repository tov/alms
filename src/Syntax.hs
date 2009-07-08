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
  Q(..),
  Lid(..), Uid(..), Ident(..), TyVar(..),

  TyTag(..), Variance(..),
  Type(..), tyC, tyA, TypeT, TEnv,
  Prog(..), ProgT,
  Decl(..), DeclT,
  Mod(..), ModT, TyDec(..), TyDecT,

  Expr(), ExprT, Expr'(..), expr',
  fv,
  exId, exStr, exInt, exCase, exLetRec, exPair,
  exAbs, exApp, exTAbs, exTApp, exCast, exUnroll,
  exVar, exCon, exLet, exSeq, -- <== synthetic
  Binding(..), BindingT, Patt(..),
  pv,

  PO(..),

  tdUnit, tdBool, tdInt, tdString, tdTuple, tdArr, tdLol,

  dualSessionType,
  tdDual, tdSend, tdRecv, tdSelect, tdFollow,

  tyGround, tyArr, tyLol, tyTuple,
  tyUnitT, tyBoolT, tyArrT, tyLolT, tyTupleT,

  ftv, freshTyVar, freshTyVars, tysubst, qualifier,
  funtypes,
  ctype2atype, atype2ctype, cgetas, agetcs,

  syntacticValue, modName, prog2decls,
  unfoldExAbs, unfoldTyAll, unfoldExTApp, unfoldExApp, unfoldTyFun
) where

import Util
import Env

import qualified Data.Map as M
import qualified Data.Set as S

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
newtype Lid = Lid { unLid :: String }
  deriving (Eq, Ord)

newtype Uid = Uid { unUid :: String }
  deriving (Eq, Ord)

data Ident = Var { unVar :: Lid }
           | Con { unCon :: Uid }
  deriving (Eq, Ord)

-- Type variables
data TyVar = TV { tvname :: Lid, tvqual :: Q }
  deriving (Eq, Ord)

-- Variance
data Variance = Invariant
              | Covariant
              | Contravariant
              | Omnivariant
  deriving (Eq, Ord)

-- Info about a type constructor (for language A)
data TyTag =
  TyTag {
    tdId    :: Integer,
    tdArity :: [Variance], -- The variance of each of its parameters
    tdQual  :: [Either Int Q],
                           -- The qualifier of the type is the lub of
                           -- the qualifiers of the named parameters and
                           -- possibly some constants
    tdTrans :: Bool
  }
  deriving Show

data Type i w where
  TyCon { tycon  :: Lid,
          tyargs :: [Type i w],
          tyinfo :: i } :: Type i w
  TyVar :: TyVar -> Type i w
  TyAll :: TyVar -> Type i w -> Type i w
  TyMu  :: TyVar -> Type i w -> Type i w
  TyC   :: Type i C -> Type i A
  TyA   :: Type i A -> Type i C

tyC :: Type i C -> Type i A
tyC (TyA t) = t
tyC t       = TyC t

tyA :: Type i A -> Type i C
tyA (TyC t) = t
tyA t       = TyA t

type TEnv w = Env Lid (TypeT w)

data Prog i = Prog [Decl i] (Expr i C)

data Decl i = DcMod (Mod i)
            | DcTyp (TyDec i)

data Mod i  = MdA Lid (Maybe (Type i A)) (Expr i A)
            | MdC Lid (Maybe (Type i C)) (Expr i C)
            | MdInt Lid (Type i A) Lid

data TyDec i = TdAbsC {
                 tdName      :: Lid,
                 tdParams    :: [TyVar]
               }
             | TdAbsA {
                 tdName      :: Lid,
                 tdParams    :: [TyVar],
                 tdVariances :: [Variance],
                 tdaQual     :: [Either TyVar Q]
               }
             | TdSynC {
                 tdName      :: Lid,
                 tdParams    :: [TyVar],
                 tdcRHS      :: Type () C
             }
             | TdSynA {
                 tdName      :: Lid,
                 tdParams    :: [TyVar],
                 tdaRHS      :: Type () A
             }
             | TdDatC {
                 tdName      :: Lid,
                 tdParams    :: [TyVar],
                 tdcAlts     :: [(Uid, Maybe (Type () C))]
             }
             | TdDatA {
                 tdName      :: Lid,
                 tdParams    :: [TyVar],
                 tdaAlts     :: [(Uid, Maybe (Type () A))]
             }

data Expr i w = Expr { fv_ :: FV, expr'_ :: Expr' i w }
type FV       = M.Map Lid Integer
data Expr' i w = ExId Ident
               | ExStr String
               | ExInt Integer
               | ExCase (Expr i w) [(Patt, Expr i w)]
               | ExLetRec [Binding i w] (Expr i w)
               | ExPair (Expr i w) (Expr i w)
               | ExAbs Patt (Type i w) (Expr i w)
               | ExApp (Expr i w) (Expr i w)
               | ExTAbs TyVar (Expr i w)
               | ExTApp (Expr i w) (Type i w)
               | ExCast (Expr i w) (Type i w) (Type i A)
               | ExUnroll (Expr i w)

data Binding i w = Binding {
  bnvar  :: Lid,
  bntype :: Type i w,
  bnexpr :: Expr i w
}

data Patt = PaWild
          | PaVar Lid
          | PaCon Uid (Maybe Patt)
          | PaPair Patt Patt
          | PaStr String
          | PaInt Integer
          | PaAs Patt Lid

type ExprT    = Expr TyTag
type TypeT    = Type TyTag
type DeclT    = Decl TyTag
type ModT     = Mod TyTag
type TyDecT   = TyDec TyTag
type BindingT = Binding TyTag
type ProgT    = Prog TyTag

fv :: Expr i w -> FV
fv  = fv_

pv :: Patt -> S.Set Lid
pv PaWild             = S.empty
pv (PaVar x)          = S.singleton x
pv (PaCon _ Nothing)  = S.empty
pv (PaCon _ (Just x)) = pv x
pv (PaPair x y)       = pv x `S.union` pv y
pv (PaStr _)          = S.empty
pv (PaInt _)          = S.empty
pv (PaAs x y)         = pv x `S.union` S.singleton y

expr' :: Expr i w -> Expr' i w
expr'  = expr'_

exStr :: String -> Expr i w
exStr  = Expr M.empty . ExStr

exInt :: Integer -> Expr i w
exInt  = Expr M.empty . ExInt

exCase  :: Expr i w -> [(Patt, Expr i w)] -> Expr i w
exCase e clauses = Expr {
  fv_    = fv e |*|
           foldl (|+|) M.empty [ fv ex |--| pv x | (x, ex) <- clauses ],
  expr'_ = ExCase e clauses
}

exLetRec :: [Binding i w] -> Expr i w -> Expr i w
exLetRec bs e2 = Expr {
  fv_    = let es  = map bnexpr bs
               vs  = map bnvar  bs
               pot = foldr (|*|) (fv e2) (map fv es)
           in foldl (|-|) pot vs,
  expr'_ = ExLetRec bs e2
}

exId :: Ident -> Expr i w
exId x = Expr {
  fv_    = case x of
             Var y -> M.singleton y 1
             Con _ -> M.empty,
  expr'_ = ExId x
}

exPair :: Expr i w -> Expr i w -> Expr i w
exPair e1 e2 = Expr {
  fv_    = fv e1 |*| fv e2,
  expr'_ = ExPair e1 e2
}

exAbs :: Patt -> Type i w -> Expr i w -> Expr i w
exAbs x t e = Expr {
  fv_    = fv e |--| pv x,
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

exCast :: Expr i w -> Type i w -> Type i A -> Expr i w
exCast e t1 t2 = Expr {
  fv_    = fv e,
  expr'_ = ExCast e t1 t2
}

exUnroll :: Expr i w -> Expr i w
exUnroll e = Expr {
  fv_    = fv e,
  expr'_ = ExUnroll e
}

exVar :: Lid -> Expr i w
exVar  = exId . Var

exCon :: Uid -> Expr i w
exCon  = exId . Con

exLet :: Patt -> Expr i w -> Expr i w -> Expr i w
exLet x e1 e2 = exCase e1 [(x, e2)]

exSeq :: Expr i w -> Expr i w -> Expr i w
exSeq e1 e2 = exCase e1 [(PaWild, e2)]

(|*|), (|+|) :: FV -> FV -> FV
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: FV -> Lid -> FV
(|-|)  = flip M.delete

(|--|) :: FV -> S.Set Lid -> FV
(|--|)  = S.fold M.delete

-----
----- Some classes and instances
-----

instance Eq TyTag where
  td == td' = tdId td == tdId td'

instance Language w => Eq (Type TyTag w) where
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
  _            == _               = False

instance Show Q where
  showsPrec _ Qa = ('A':)
  showsPrec _ Qu = ('U':)

instance Show Variance where
  showsPrec _ Invariant     = ('1':)
  showsPrec _ Covariant     = ('+':)
  showsPrec _ Contravariant = ('-':)
  showsPrec _ Omnivariant   = ('0':)

instance Show Lid where
  show = unLid

instance Show Uid where
  show = unUid

instance Show Ident where
  show (Var x) = show x
  show (Con k) = show k

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

instance Language w => PO (Type TyTag w) where
  -- Special cases for dual session types:
  ifMJ b (TyCon _ [p] td) t | td == tdDual = ifMJ b (dualSessionType p) t
  ifMJ b t (TyCon _ [p] td) | td == tdDual = ifMJ b t (dualSessionType p)
  -- Special cases for ->/-o subtyping:
  ifMJ b (TyCon _ ps td) (TyCon _ ps' td')
    | td == tdArr && td' == tdLol || td == tdLol && td' == tdArr
      = ifMJ b (build ps) (build ps')
    where build ps0 = if b
                        then TyCon (Lid "-o") ps0 tdLol
                        else TyCon (Lid "->") ps0 tdArr
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
  ifMJ _ t t' =
    if t == t'
      then return t
      else fail "\\/? or /\\?: Does not exist"

ifMJBind :: (Monad m, Language w) =>
            (TyVar -> TypeT w -> TypeT w) -> Bool ->
            (TyVar, TypeT w) -> (TyVar, TypeT w) ->
            m (TypeT w)
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
  langMapType x    = fmap tyA x

instance Language A where
  type OtherLang A = C
  reifyLang        = A
  langCase x _ fa  = fa x
  langMapType x    = fmap tyC x

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

ftv :: TypeT w -> M.Map TyVar Variance
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
    attach n = tv { tvname = Lid (unLid (tvname tv) ++ show n) }
    loop    :: Int -> TyVar
    loop n   =
      let tv' = attach n
      in if tv' `M.member` m
           then loop (n + 1)
           else tv'

tysubst :: (Language w, Language w') =>
           TyVar -> TypeT w' -> TypeT w -> TypeT w
tysubst a t = ts where
  ts :: Language w => TypeT w -> TypeT w
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
                = tyA (ts t')
  ts (TyC t')
                = tyC (ts t')

-- Helper for finding the dual of a session type (since we can't
-- express this direction in the type system)
dualSessionType :: TypeT w -> TypeT w
dualSessionType  = d where
  d (TyCon (Lid "->") [TyCon (Lid "send") [ta] _, tr] _)
    = TyCon (Lid "->") [TyCon (Lid "recv") [ta] tdRecv, d tr] tdArr
  d (TyCon (Lid "->") [TyCon (Lid "recv") [ta] _, tr] _)
    = TyCon (Lid "->") [TyCon (Lid "send") [ta] tdSend, d tr] tdArr
  d (TyCon (Lid "select") [TyCon (Lid "*") [t1, t2] _] _)
    = TyCon (Lid "follow") [TyCon (Lid "*") [d t1, d t2] tdTuple] tdFollow
  d (TyCon (Lid "follow") [TyCon (Lid "*") [t1, t2] _] _)
    = TyCon (Lid "select") [TyCon (Lid "*") [d t1, d t2] tdTuple] tdSelect
  d (TyMu tv t)
    = TyMu tv (d t)
  d t = t

tdUnit, tdBool, tdInt, tdString,
  tdArr, tdLol, tdTuple :: TyTag

tdUnit       = TyTag (-1)  []          []                True
tdBool       = TyTag (-2)  []          []                True
tdInt        = TyTag (-3)  []          []                True
tdString     = TyTag (-4)  []          []                True
tdArr        = TyTag (-5)  [-1, 1]     []                False
tdLol        = TyTag (-6)  [-1, 1]     [Right Qa]        False
tdTuple      = TyTag (-7)  [1, 1]      [Left 0, Left 1]  False

tdDual, tdSend, tdRecv, tdSelect, tdFollow :: TyTag
-- For session types:
tdDual       = TyTag (-11) [-1] []                False
tdSend       = TyTag (-12) [1]  []                False
tdRecv       = TyTag (-13) [-1] []                False
tdSelect     = TyTag (-14) [1]  []                False
tdFollow     = TyTag (-15) [1]  []                False

tyGround      :: String -> Type () w
tyGround s     = TyCon (Lid s) [] ()

tyArr         :: Type () w -> Type () w -> Type () w
tyArr a b      = TyCon (Lid "->") [a, b] ()

tyLol         :: Type () w -> Type () w -> Type () w
tyLol a b      = TyCon (Lid "-o") [a, b] ()

tyTuple       :: Type () w -> Type () w -> Type () w
tyTuple a b    = TyCon (Lid "*") [a, b] ()

tyUnitT        :: TypeT w
tyUnitT         = TyCon (Lid "unit") [] tdUnit

tyBoolT        :: TypeT w
tyBoolT         = TyCon (Lid "bool") [] tdBool

tyArrT         :: TypeT w -> TypeT w -> TypeT w
tyArrT a b      = TyCon (Lid "->") [a, b] tdArr

tyLolT         :: TypeT w -> TypeT w -> TypeT w
tyLolT a b      = TyCon (Lid "-o") [a, b] tdLol

tyTupleT       :: TypeT w -> TypeT w -> TypeT w
tyTupleT a b    = TyCon (Lid "*") [a, b] tdTuple

qualifier     :: TypeT A -> Q
qualifier (TyCon _ ps td) = foldl max minBound qs' where
  qs = map qualifier ps
  toQ (Left ix) = qs !! ix
  toQ (Right q) = q
  qs' = map toQ (tdQual td)
qualifier (TyVar (TV _ q))   = q
qualifier (TyAll _ t)        = qualifier t
qualifier (TyMu _ t)         = qualifier t
qualifier _                  = Qu

-- Funtional types
funtypes    :: [TyTag]
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

ctype2atype :: TypeT C -> TypeT A
ctype2atype (TyCon n ps td) | tdTrans td
  = TyCon n (map ctype2atype ps) td
ctype2atype (TyCon _ [td, tr] d) | d == tdArr
  = TyCon (Lid "->") [ctype2atype td, ctype2atype tr] tdArr
ctype2atype (TyAll tv t)
                      = TyAll tv (ctype2atype t')
                        where t'  = tysubst tv (tyA (TyVar tv)) t
ctype2atype (TyMu tv t)
                      = TyMu tv (ctype2atype t')
                        where t'  = tysubst tv (tyA (TyVar tv)) t
ctype2atype t         = tyC t

atype2ctype :: TypeT A -> TypeT C
atype2ctype (TyCon n ps td) | tdTrans td
  = TyCon n (map atype2ctype ps) td
atype2ctype (TyCon _ [td, tr] d) | d `elem` funtypes
  = TyCon (Lid "->") [atype2ctype td, atype2ctype tr] tdArr
atype2ctype (TyAll tv t)
                      = TyAll tv (atype2ctype t')
                        where t' = tysubst tv (tyC (TyVar tv)) t
atype2ctype (TyMu tv t)
                      = TyMu tv (atype2ctype t')
                        where t' = tysubst tv (tyC (TyVar tv)) t
atype2ctype t         = tyA t

syntacticValue :: Expr i w -> Bool
syntacticValue e = case expr' e of
  ExId _       -> True
  ExStr _      -> True
  ExInt _      -> True
  ExPair e1 e2 -> syntacticValue e1 && syntacticValue e2
  ExAbs _ _ _  -> True
  ExTAbs _ _   -> True
  ExTApp e1 _  -> syntacticValue e1
  ExUnroll e1  -> syntacticValue e1
  _            -> False

modName :: Mod i -> Lid
modName (MdA x _ _)   = x
modName (MdC x _ _)   = x
modName (MdInt x _ _) = x

prog2decls :: Prog i -> [Decl i]
prog2decls (Prog ds e) = ds ++ [DcMod (MdC (Lid "it") Nothing e)]

-- Unfolding various sequences

unfoldExAbs :: Expr i w -> ([Either (Patt, Type i w) TyVar], Expr i w)
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

unfoldTyFun :: TypeT w -> ([TypeT w], TypeT w)
unfoldTyFun  = unscanr each where
  each (TyCon _ [ta, tr] td) | td `elem` funtypes = Just (ta, tr)
  each _                                         = Nothing
