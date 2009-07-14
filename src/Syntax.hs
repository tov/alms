{-# LANGUAGE
      DeriveDataTypeable,
      EmptyDataDecls,
      FlexibleContexts,
      FlexibleInstances,
      GADTs,
      ParallelListComp,
      RankNTypes,
      ScopedTypeVariables,
      TypeFamilies #-}
module Syntax (
  Language(..), A, C, LangRep(..),
  Q(..),
  Lid(..), Uid(..), Ident(..), TyVar(..),

  TyTag(..), Variance(..),
  Type(..), tyC, tyA, TypeT, TEnv,
  Prog(..), ProgT,
  Decl(..), DeclT,
  Mod(..), ModT, TyDec(..), AbsTy(..),

  TypeTW(..), typeTW,

  Expr(), ExprT, Expr'(..), expr',
  fv,
  exId, exStr, exInt, exCase, exLetRec, exPair,
  exAbs, exApp, exTAbs, exTApp, exCast,
  exVar, exCon, exLet, exSeq, -- <== synthetic
  Binding(..), BindingT, Patt(..),
  pv,

  PO(..), bigVee, bigVeeM, bigWedge, bigWedgeM,

  tdUnit, tdBool, tdInt, tdString, tdTuple, tdArr, tdLol,

  dualSessionType,
  tdDual, tdSend, tdRecv, tdSelect, tdFollow,

  tyGround, tyArr, tyLol, tyTuple,
  tyUnitT, tyBoolT, tyArrT, tyLolT, tyTupleT,

  Ftv(..), freshTyVar, freshTyVars, tysubst, tysubst1, qualifier,
  funtypes,
  ctype2atype, atype2ctype, cgetas, agetcs, replaceTyTags,

  syntacticValue, castableType, modName, prog2decls,
  unfoldExAbs, unfoldTyAll, unfoldExTApp, unfoldExApp, unfoldTyFun,

  dumpType
) where

import Util
import Env

import Control.Monad.State (State, evalState, get, put)
import Data.Char (isAlpha, isDigit)
import qualified Data.Map as M
import qualified Data.Set as S

import Data.Generics (Typeable(..), Data(..), Fixity(..),
                      Constr, mkConstr, constrIndex,
                      DataType, mkDataType,
                      everywhere, mkT)

-- We have two languages:
data C deriving Typeable
data A deriving Typeable

data LangRep w where
  A :: LangRep A
  C :: LangRep C

-- Qualifiers
data Q = Qa | Qu
  deriving (Eq, Typeable, Data)

-- Variables
newtype Lid = Lid { unLid :: String }
  deriving (Eq, Ord, Typeable, Data)

newtype Uid = Uid { unUid :: String }
  deriving (Eq, Ord, Typeable, Data)

data Ident = Var { unVar :: Lid }
           | Con { unCon :: Uid }
  deriving (Eq, Ord, Typeable, Data)

-- Type variables
data TyVar = TV { tvname :: Lid, tvqual :: Q }
  deriving (Eq, Ord, Typeable, Data)

-- Variance
data Variance = Invariant
              | Covariant
              | Contravariant
              | Omnivariant
  deriving (Eq, Ord, Typeable, Data)

-- Info about a type constructor (for language A)
data TyTag =
  TyTag {
    ttId    :: Integer,
    ttArity :: [Variance], -- The variance of each of its parameters
    ttQual  :: [Either Int Q],
                           -- The qualifier of the type is the lub of
                           -- the qualifiers of the named parameters and
                           -- possibly some constants
    ttTrans :: Bool
  }
  deriving (Show, Typeable, Data)

data Type i w where
  TyCon { tycon  :: Lid,
          tyargs :: [Type i w],
          tyinfo :: i } :: Type i w
  TyVar :: TyVar -> Type i w
  TyAll :: TyVar -> Type i w -> Type i w
  TyMu  :: TyVar -> Type i w -> Type i w
  TyC   :: Type i C -> Type i A
  TyA   :: Type i A -> Type i C
  deriving Typeable

tyC :: Type i C -> Type i A
tyC (TyA t) = t
tyC t       = TyC t

tyA :: Type i A -> Type i C
tyA (TyC t) = t
tyA t       = TyA t

type TEnv w = Env Lid (TypeT w)

data Prog i = Prog [Decl i] (Maybe (Expr i C))
  deriving (Typeable, Data)

data Decl i = DcMod (Mod i)
            | DcTyp TyDec
            | DcAbs AbsTy [Decl i]
  deriving (Typeable, Data)

data Mod i  = MdA Lid (Maybe (Type i A)) (Expr i A)
            | MdC Lid (Maybe (Type i C)) (Expr i C)
            | MdInt Lid (Type i A) Lid
  deriving (Typeable, Data)

data TyDec   = TdAbsC {
                 tdName      :: Lid,
                 tdParams    :: [TyVar]
               }
             | TdAbsA {
                 tdName      :: Lid,
                 tdParams    :: [TyVar],
                 tdVariances :: [Variance],
                 tdQual      :: [Either TyVar Q]
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
  deriving (Typeable, Data)

data AbsTy   = AbsTyC {
                 atName      :: Lid,
                 atParams    :: [TyVar],
                 atcAlts     :: [(Uid, Maybe (Type () C))]
               }
             | AbsTyA {
                 atName      :: Lid,
                 atParams    :: [TyVar],
                 atVariances :: [Variance],
                 atQual      :: [Either TyVar Q],
                 atAlts      :: [(Uid, Maybe (Type () A))]
               }
  deriving (Typeable, Data)

data Expr i w = Expr { fv_ :: FV, expr'_ :: Expr' i w }
  deriving (Typeable, Data)
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
  deriving (Typeable, Data)

data Binding i w = Binding {
  bnvar  :: Lid,
  bntype :: Type i w,
  bnexpr :: Expr i w
}
  deriving (Typeable, Data)

data Patt = PaWild
          | PaVar Lid
          | PaCon Uid (Maybe Patt)
          | PaPair Patt Patt
          | PaStr String
          | PaInt Integer
          | PaAs Patt Lid
  deriving (Typeable, Data)

type ExprT    = Expr TyTag
type TypeT    = Type TyTag
type DeclT    = Decl TyTag
type ModT     = Mod TyTag
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

instance Data C where
  gfoldl _ _ _  = error "gfoldl(C): uninhabited"
  gunfold _ _ _ = error "gunfold(C): uninhabited"
  toConstr _    = error "toConstr(C): uninhabited"
  dataTypeOf _ = ty_C

instance Data A where
  gfoldl _ _ _  = error "gfoldl(A): uninhabited"
  gunfold _ _ _ = error "gunfold(A): uninhabited"
  toConstr _    = error "toConstr(A): uninhabited"
  dataTypeOf _ = ty_A

ty_C, ty_A :: DataType
ty_C  = mkDataType "Syntax.C" [ ]
ty_A  = mkDataType "Syntax.A" [ ]

instance (Language w, Data i, Data w) => Data (Type i w) where
   gfoldl k z (TyCon a b c) = z TyCon `k` a `k` b `k` c
   gfoldl k z (TyVar a)     = z TyVar `k` a
   gfoldl k z (TyAll a b)   = z TyAll `k` a `k` b
   gfoldl k z (TyMu a b)    = z TyMu  `k` a `k` b
   gfoldl k z (TyC a)       = z TyC   `k` a
   gfoldl k z (TyA a)       = z TyA   `k` a

   gunfold k z c = case constrIndex c of
                       1 -> k $ k $ k $ z TyCon
                       2 -> k $ z TyVar
                       3 -> k $ k $ z TyAll
                       4 -> k $ k $ z TyMu
                       5 -> k $ z unTyC
                       6 -> k $ z unTyA
                       _ -> error "gunfold(Type): bad constrIndex"

   toConstr (TyCon _ _ _) = con_TyCon
   toConstr (TyVar _)     = con_TyVar
   toConstr (TyAll _ _)   = con_TyAll
   toConstr (TyMu _ _)    = con_TyMu
   toConstr (TyC _)       = con_TyC
   toConstr (TyA _)       = con_TyA

   dataTypeOf _ = ty_Type

unTyC :: forall w i. Language w => Type i C -> Type i w
unTyC t = case reifyLang :: LangRep w of
            C -> t
            A -> tyC t

unTyA :: forall w i. Language w => Type i A -> Type i w
unTyA t = case reifyLang :: LangRep w of
            C -> tyA t
            A -> t

con_TyCon, con_TyVar, con_TyAll, con_TyMu, con_TyC, con_TyA
        :: Constr
ty_Type :: DataType
con_TyCon = mkConstr ty_Type "TyCon" [] Prefix
con_TyVar = mkConstr ty_Type "TyVar" [] Prefix
con_TyAll = mkConstr ty_Type "TyAll" [] Prefix
con_TyMu  = mkConstr ty_Type "TyMu"  [] Prefix
con_TyC   = mkConstr ty_Type "TyC"   [] Prefix
con_TyA   = mkConstr ty_Type "TyA"   [] Prefix
ty_Type = mkDataType "Syntax.Type"
            [ con_TyCon, con_TyVar, con_TyAll, con_TyMu, con_TyC, con_TyA ]

instance Eq TyTag where
  td == td' = ttId td == ttId td'

data TypeTW = TypeTC (TypeT C)
            | TypeTA (TypeT A)

typeTW :: Language w => TypeT w -> TypeTW
typeTW t = langCase t TypeTC TypeTA

-- On TypeTW, we define simple alpha equality, which we then use
-- to keep track of where we've been when we define type equality
-- that understands mu.
instance Eq TypeTW where
  tw1 == tw2 = case (tw1, tw2) of
                 (TypeTC t1, TypeTC t2) -> t1 === t2
                 (TypeTA t1, TypeTA t2) -> t1 === t2
                 (TypeTC _ , TypeTA _ ) -> False
                 (TypeTA _ , TypeTC _ ) -> False
    where
      (===) :: Language w => TypeT w -> TypeT w -> Bool
      TyCon _ ps td === TyCon _ ps' td'
                                 = td == td' && all2 (===) ps ps'
      TyA t         === TyA t'   = t === t'
      TyC t         === TyC t'   = t === t'
      TyVar x       === TyVar x' = x == x'
      TyAll x t     === TyAll x' t'
        | tvqual x == tvqual x' =
          tysubst1 x a t === tysubst1 x' a t'
            where a = TyVar (freshTyVar x (ftv [t, t']))
      TyMu x t      === TyMu x' t'
        | tvqual x == tvqual x' =
          tysubst1 x a t === tysubst1 x' a t'
            where a = TyVar (freshTyVar x (ftv [t, t']))
      _             === _        = False

instance Language w => Eq (Type TyTag w) where
  (==) t1i t2i = evalState (t1i `chk` t2i) [] where
    chk, cmp :: Language w' =>
                TypeT w' -> TypeT w' -> State [(TypeTW, TypeTW)] Bool
    t1 `chk` t2 = do
      seen <- get
      let tw1 = typeTW t1; tw2 = typeTW t2
      if (tw1, tw2) `elem` seen
        then return True
        else do
          put ((tw1, tw2) : (tw2, tw1) : seen)
          cmp t1 t2

    TyCon _ [p] td `cmp` t
      | td == tdDual                     = dualSessionType p `chk` t
    t              `cmp` TyCon _ [p] td
      | td == tdDual                     = t `chk` dualSessionType p
    TyMu a t       `cmp` t'              = tysubst a (TyMu a t) t `chk` t'
    t'             `cmp` TyMu a t        = t' `chk` tysubst a (TyMu a t) t
    TyCon _ ps td  `cmp` TyCon _ ps' td'
      | td == td'   = allM2 chk ps ps'
    TyA t          `cmp` TyA t'          = t `chk` t'
    TyC t          `cmp` TyC t'          = t `chk` t'
    TyVar x        `cmp` TyVar x'        = return (x == x')
    TyAll x t      `cmp` TyAll x' t' 
      | tvqual x == tvqual x'            = 
        tysubst1 x a t `chk` tysubst1 x' a t'
          where a = TyVar (freshTyVar x (ftv [t, t']))
    _            `cmp` _               = return False

instance Show Q where
  showsPrec _ Qa = ('A':)
  showsPrec _ Qu = ('U':)

instance Show Variance where
  showsPrec _ Invariant     = ('1':)
  showsPrec _ Covariant     = ('+':)
  showsPrec _ Contravariant = ('-':)
  showsPrec _ Omnivariant   = ('0':)

instance Show Lid where
  showsPrec _ (Lid s) = case s of
    '_':_             -> (s++)
    c  :_ | isAlpha c -> (s++)
    '*':_             -> ("( "++) . (s++) . (" )"++)
    _                 -> ('(':) . (s++) . (')':)

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

bigVee :: (Bounded a, PO a) => [a] -> a
bigVee  = foldr (\/) minBound

bigVeeM :: (Monad m, Bounded a, PO a) => [a] -> m a
bigVeeM  = foldrM (\/?) minBound

bigWedge :: (Bounded a, PO a) => [a] -> a
bigWedge  = foldr (/\) maxBound

bigWedgeM :: (Monad m, Bounded a, PO a) => [a] -> m a
bigWedgeM  = foldrM (/\?) maxBound

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

  -- Special cases for dual session types:
instance  PO (Type TyTag A) where
  ifMJ bi t1i t2i = clean `liftM` chk [] bi t1i t2i where
    clean :: TypeT w -> TypeT w
    clean (TyCon c ps td)  = TyCon c (map clean ps) td
    clean (TyVar a)        = TyVar a
    clean (TyAll a t)      = TyAll a (clean t)
    clean (TyMu a t)
      | a `M.member` ftv t = TyMu a (clean t)
      | otherwise          = clean t
    clean (TyC t)          = tyC (clean t)
    clean (TyA t)          = tyA (clean t)

    chk, cmp :: Monad m =>
                [((Bool, TypeTW, TypeTW), TyVar)] ->
                Bool -> TypeT A -> TypeT A ->
                m (TypeT A)
    chk seen b t1 t2 = do
      let tw1 = typeTW t1; tw2 = typeTW t2
      case lookup (b, tw1, tw2) seen of
        Just tv -> return (TyVar tv)
        Nothing -> TyMu tv `liftM` cmp seen' b t1 t2 where
          used  = M.fromList [ (a, 1) | (_, a) <- seen ]
          tv    = freshTyVar (TV (Lid "r") (qualifier t1 \/ qualifier t2))
                             (ftv [t1, t2] `M.union` used)
          seen' = (((b, tw1, tw2), tv) : ((b, tw2, tw1), tv) : seen)

    -- Special cases for session types duality:
    cmp seen b (TyCon _ [p] td) t
      | td == tdDual                = chk seen b (dualSessionType p) t
    cmp seen b t (TyCon _ [p] td)
      | td == tdDual                = chk seen b t (dualSessionType p)
    -- Special cases for ->/-o subtyping:
    cmp seen b (TyCon _ ps td) (TyCon _ ps' td')
      | (td == tdArr && td' == tdLol) || (td == tdLol && td' == tdArr)
                                    = chk seen b (build ps) (build ps')
          where build ps0 = if b
                              then TyCon (Lid "-o") ps0 tdLol
                              else TyCon (Lid "->") ps0 tdArr
    -- Otherwise:
    cmp seen b (TyCon tc ps td) (TyCon _ ps' td') =
      if td == td' then do
        params <- sequence
          [ case var of
              Covariant     -> chk seen b p p'
              Contravariant -> chk seen (not b) p p'
              _             -> if p == p'
                               then return p
                               else fail "\\/? or /\\?: Does not exist"
             | var <- ttArity td
             | p   <- ps
             | p'  <- ps' ]
        return (TyCon tc params td)
      else fail "\\/? or /\\?: Does not exist"
    cmp seen b (TyAll a t)   (TyAll a' t')  = do
      qual <- ifMJ (not b) (tvqual a) (tvqual a')
      let a1  = a { tvqual = qual } `freshTyVar` (ftv [t, t'])
          t1  = tysubst1 a (TyVar a1) t
          t'1 = tysubst1 a' (TyVar a1) t'
      TyAll a1 `liftM` chk seen b t1 t'1
    cmp seen b (TyMu a t) t' = chk seen b (tysubst a (TyMu a t) t) t'
    cmp seen b t' (TyMu a t) = chk seen b t' (tysubst a (TyMu a t) t)
    cmp _    _ t t' =
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

class Ftv a where
  ftv :: a -> M.Map TyVar Variance

instance Ftv (Type TyTag w) where
  ftv (TyCon _ ts td)= M.unionsWith (+)
                         [ M.map (* var) m
                         | var <- ttArity td
                         | m   <- map ftv ts ]
  ftv (TyVar tv)     = M.singleton tv 1
  ftv (TyAll tv t)   = M.delete tv (ftv t)
  ftv (TyMu tv t)    = M.delete tv (ftv t)
  ftv (TyC t)        = M.map (const Invariant)
                             (M.unions (map ftv (cgetas t)))
  ftv (TyA t)        = M.map (const Invariant)
                             (M.unions (map ftv (agetcs t)))

instance Ftv a => Ftv [a] where
  ftv = M.unionsWith (+) . map ftv

freshTyVars :: [TyVar] -> M.Map TyVar a -> [TyVar]
freshTyVars tvs0 m0 = loop tvs0 m1 where
  m1 = M.union (M.map (const ()) m0)
               (M.fromList [ (tv, ()) | tv <- tvs0 ])
  loop (tv:tvs) m' = let tv' = freshTyVar tv m'
                      in tv' : loop tvs (M.insert tv' () m')
  loop _        _ = []

freshTyVar :: TyVar -> M.Map TyVar a -> TyVar
freshTyVar tv m = if tv `M.member` m
                    then loop count
                    else tv
  where
    suffix   = reverse . takeWhile isDigit . reverse . unLid $ tvname tv
    prefix   = reverse . dropWhile isDigit . reverse . unLid $ tvname tv
    count    = case reads suffix of
                 ((n, ""):_) -> n
                 _           -> 0
    attach n = tv { tvname = Lid (prefix ++ show n) }
    loop    :: Int -> TyVar
    loop n   =
      let tv' = attach n
      in if tv' `M.member` m
           then loop (n + 1)
           else tv'

tysubst1 :: Language w => TyVar -> TypeT w -> TypeT w -> TypeT w
tysubst1  = tysubst

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
                          let a'' = freshTyVar a' (ftv [t, t'])
                           in TyAll a'' (ts (tysubst1 a' (TyVar a'') t')))
                    (TyAll a' (ts t'))
  ts (TyMu a' t')
                = sameLang t' t
                    (\_ _ ->
                      if a' == a
                        then TyMu a' t'
                        else
                          let a'' = freshTyVar a' (ftv [t, t'])
                          in TyMu a'' (ts (tysubst1 a' (TyVar a'') t')))
                    (TyMu a' (ts t'))
  ts (TyCon c tys td)
                = TyCon c (map ts tys) td
  ts (TyA t')
                = atype2ctype (ts t')
  ts (TyC t')
                = ctype2atype (ts t')

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

infixr 8 `tyArrT`, `tyLolT`
infixl 7 `tyTupleT`

qualifier     :: TypeT A -> Q
qualifier (TyCon _ ps td) = foldl max minBound qs' where
  qs = map qualifier ps
  toQ (Left ix) = qs !! ix
  toQ (Right q) = q
  qs' = map toQ (ttQual td)
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

replaceTyTags :: Data a => TyTag -> a -> a
replaceTyTags tag' = everywhere (mkT each) where
  each :: TyTag -> TyTag
  each tag | ttId tag == ttId tag' = tag'
           | otherwise             = tag

ctype2atype :: TypeT C -> TypeT A
ctype2atype (TyCon n ps td) | ttTrans td
  = TyCon n (map ctype2atype ps) td
ctype2atype (TyCon _ [td, tr] d) | d == tdArr
  = TyCon (Lid "->") [ctype2atype td, ctype2atype tr] tdArr
ctype2atype (TyAll tv t)
                      = TyAll tv' (ctype2atype t')
                        where t'  = tysubst tv (tyA (TyVar tv')) t
                              tv' = tv { tvqual = Qu } `freshTyVar` ftv t
ctype2atype (TyMu tv t)
                      = TyMu tv' (ctype2atype t')
                        where t'  = tysubst tv (tyA (TyVar tv')) t
                              tv' = tv { tvqual = Qu } `freshTyVar` ftv t
ctype2atype t         = tyC t

atype2ctype :: TypeT A -> TypeT C
atype2ctype (TyCon n ps td) | ttTrans td
  = TyCon n (map atype2ctype ps) td
atype2ctype (TyCon _ [td, tr] d) | d `elem` funtypes
  = TyCon (Lid "->") [atype2ctype td, atype2ctype tr] tdArr
atype2ctype (TyAll tv t)
                      = TyAll tv' (atype2ctype t')
                        where t' = tysubst tv (tyC (TyVar tv')) t
                              tv' = tv { tvqual = Qu } `freshTyVar` ftv t
atype2ctype (TyMu tv t)
                      = TyMu tv' (atype2ctype t')
                        where t' = tysubst tv (tyC (TyVar tv')) t
                              tv' = tv { tvqual = Qu } `freshTyVar` ftv t
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
  _            -> False

castableType :: TypeT w -> Bool
castableType (TyVar _)      = False
castableType (TyCon _ _ td) = td `elem` funtypes
castableType (TyAll _ t)    = castableType t
castableType (TyMu _ t)     = castableType t
castableType (TyC _)        = False
castableType (TyA _)        = False

modName :: Mod i -> Lid
modName (MdA x _ _)   = x
modName (MdC x _ _)   = x
modName (MdInt x _ _) = x

prog2decls :: Prog i -> [Decl i]
prog2decls (Prog ds (Just e)) = ds ++ [DcMod (MdC (Lid "it") Nothing e)]
prog2decls (Prog ds Nothing)  = ds

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

dumpType :: Int -> TypeT w -> IO ()
dumpType i t0 = do
  putStr (replicate i ' ')
  case t0 of
    TyCon n ps td -> do
      putStrLn $ show n ++ " [" ++ show td ++ "] {"
      mapM_ (dumpType (i + 2)) ps
      putStrLn (replicate i ' ' ++ "}")
    TyVar tv -> print tv
    TyAll a t -> do
      print $ "all " ++ show a ++ ". {"
      dumpType (i + 2) t
      putStrLn (replicate i ' ' ++ "}")
    TyMu a t -> do
      print $ "mu " ++ show a ++ ". {"
      dumpType (i + 2) t
      putStrLn (replicate i ' ' ++ "}")
    TyC t -> do
      print $ "TyC {"
      dumpType (i + 2) t
      putStrLn (replicate i ' ' ++ "}")
    TyA t -> do
      print $ "TyA {"
      dumpType (i + 2) t
      putStrLn (replicate i ' ' ++ "}")
