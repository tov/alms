{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE
      DeriveDataTypeable,
      EmptyDataDecls,
      FlexibleContexts,
      FlexibleInstances,
      GADTs,
      MultiParamTypeClasses,
      ParallelListComp,
      RankNTypes,
      ScopedTypeVariables,
      TypeFamilies #-}
module Syntax (
  Language, A, C, Language'(..), SameLang, LangRep(..),
  Q(..),

  Path(..),
  Lid(..), Uid(..), BIdent(..),
  Ident, QLid, QUid,
  TyVar(..),

  TyTag(..), Variance(..),
  QualSet, qsConst, qsVar, qsVars, qsFromListM, qsFromList, qsToList,
  Type(..), tyC, tyA, tyAll, tyEx, TypeT,
  removeTyTags,
  Quant(..),
  Prog(..), ProgT,

  Decl(..), DeclT, dcLet, dcTyp, dcAbs, dcMod, dcOpn, dcLoc,
  Let(..), LetT,
  TyDec(..), TyDecC(..), TyDecA(..),
  AbsTy(..),
  ModExp(..), ModExpT,

  TypeTW(..), typeTW,

  Expr(), ExprT, Expr'(..),
  fv,
  exId, exStr, exInt, exFloat, exCase, exLetRec, exLetDecl, exPair,
  exAbs, exApp, exTAbs, exTApp, exPack, exCast,
  exVar, exCon, exBVar, exBCon, exLet, exSeq, -- <== synthetic
  qlid, quid,
  Binding(..), BindingT, Patt(..),
  pv,

  PO(..), bigVee, bigVeeM, bigWedge, bigWedgeM,

  tdUnit, tdBool, tdInt, tdFloat, tdString, tdTuple, tdArr, tdLol,

  dualSessionType,
  tdDual, tdSend, tdRecv, tdSelect, tdFollow,

  tyGround, tyArr, tyLol, tyTuple,
  tyUnitT, tyBoolT, tyArrT, tyLolT, tyTupleT,

  Ftv(..), freshTyVar, freshTyVars, tysubst, tysubst1, qualifier,
  funtypes,
  ctype2atype, atype2ctype, cgetas, agetcs, replaceTyTags,

  syntacticValue, castableType, letName, prog2decls,
  unfoldExAbs, unfoldTyQu, unfoldExTApp, unfoldExApp, unfoldTyFun,

  module Viewable,
  dumpType
) where

import Util
import Env ((:>:)(..), Path(..))
import Loc as Loc
import Viewable

import Control.Monad.State (State, evalState, get, put)
import Control.Monad.Identity (runIdentity)
import Data.Char (isAlpha, isDigit)
import Data.List (elemIndex)
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

-- Usage Qualifiers
data Q = Qa | Qu
  deriving (Eq, Typeable, Data)

-- Variables
newtype Lid = Lid { unLid :: String }
  deriving (Eq, Ord, Typeable, Data)

newtype Uid = Uid { unUid :: String }
  deriving (Eq, Ord, Typeable, Data)

data BIdent = Var { unVar :: Lid }
            | Con { unCon :: Uid }
  deriving (Eq, Ord, Typeable, Data)

type QUid  = Path Uid Uid
type QLid  = Path Uid Lid
type Ident = Path Uid BIdent

-- Type variables
data TyVar = TV { tvname :: Lid, tvqual :: Q }
  deriving (Eq, Ord, Typeable, Data)

-- Variance
data Variance = Invariant
              | Covariant
              | Contravariant
              | Omnivariant
  deriving (Eq, Ord, Typeable, Data)

data QualSet = QualSet Q (S.Set Int)
  deriving (Typeable, Data)

-- Info about a type constructor (for language A)
data TyTag =
  TyTag {
    ttId    :: Integer,
    ttArity :: [Variance], -- The variance of each of its parameters
    ttQual  :: QualSet,
                           -- The qualifier of the type is the lub of
                           -- the qualifiers of the named parameters and
                           -- possibly some constants
    ttTrans :: Bool
  }
  deriving (Show, Typeable, Data)

data Type i w where
  TyCon { tycon  :: QLid,
          tyargs :: [Type i w],
          tyinfo :: i } :: Type i w
  TyVar :: TyVar -> Type i w
  TyQu  :: Quant -> TyVar -> Type i w -> Type i w
  TyMu  :: TyVar -> Type i w -> Type i w
  TyC   :: Type i C -> Type i A
  TyA   :: Type i A -> Type i C
  deriving Typeable

data Quant = Forall | Exists
  deriving (Typeable, Data, Eq)

tyC :: Type i C -> Type i A
tyC (TyA t) = t
tyC t       = TyC t

tyA :: Type i A -> Type i C
tyA (TyC t) = t
tyA t       = TyA t

tyAll, tyEx :: TyVar -> Type i w -> Type i w
tyAll = TyQu Forall
tyEx  = TyQu Exists

removeTyTags :: Type i w -> Type () w
removeTyTags  = untype where
  untype :: Type i w -> Type () w
  untype (TyCon con args _) = TyCon con (map untype args) ()
  untype (TyVar tv)         = TyVar tv
  untype (TyQu quant tv t)  = TyQu quant tv (untype t)
  untype (TyMu tv t)        = TyMu tv (untype t)
  untype (TyC t)            = TyC (untype t)
  untype (TyA t)            = TyA (untype t)

data Prog i = Prog [Decl i] (Maybe (Expr i C))
  deriving (Typeable, Data)

data Decl i = DcLet Loc (Let i)
            | DcTyp Loc TyDec
            | DcAbs Loc AbsTy [Decl i]
            | DcMod Loc Uid (ModExp i)
            | DcOpn Loc (ModExp i)
            | DcLoc Loc [Decl i] [Decl i]
  deriving (Typeable, Data)

dcLet :: Let i -> Decl i
dcLet  = DcLet bogus

dcTyp :: TyDec -> Decl i
dcTyp  = DcTyp bogus

dcAbs :: AbsTy -> [Decl i] -> Decl i
dcAbs  = DcAbs bogus

dcMod :: Uid -> ModExp i -> Decl i
dcMod  = DcMod bogus

dcOpn :: ModExp i -> Decl i
dcOpn  = DcOpn bogus

dcLoc :: [Decl i] -> [Decl i] -> Decl i
dcLoc  = DcLoc bogus

data Let i  = LtA Bool Lid (Maybe (Type i A)) (Expr i A)
            | LtC Bool Lid (Maybe (Type i C)) (Expr i C)
            | LtInt Bool Lid (Type i A) QLid
  deriving (Typeable, Data)

data TyDec   = TyDecC Bool [TyDecC]
             | TyDecA Bool [TyDecA]
  deriving (Typeable, Data)

data TyDecC  = TdAbsC {
                 tdcName      :: Lid,
                 tdcParams    :: [TyVar]
               }
             | TdSynC {
                 tdcName      :: Lid,
                 tdcParams    :: [TyVar],
                 tdcRHS       :: Type () C
             }
             | TdDatC {
                 tdcName      :: Lid,
                 tdcParams    :: [TyVar],
                 tdcAlts      :: [(Uid, Maybe (Type () C))]
             }
  deriving (Typeable, Data)
data TyDecA  = TdAbsA {
                 tdaName      :: Lid,
                 tdaParams    :: [TyVar],
                 tdaVariances :: [Variance],
                 tdaQual      :: [Either TyVar Q]
               }
             | TdSynA {
                 tdaName      :: Lid,
                 tdaParams    :: [TyVar],
                 tdaRHS       :: Type () A
             }
             | TdDatA {
                 tdaName      :: Lid,
                 tdaParams    :: [TyVar],
                 tdaAlts      :: [(Uid, Maybe (Type () A))]
             }
  deriving (Typeable, Data)

data AbsTy   = AbsTyC {
                 atTopLevel    :: Bool,
                 atTyDecC      :: [TyDecC]
               }
             | AbsTyA {
                 atTopLevel    :: Bool,
                 atTyDecA      :: [AbsTyADat]
               }
  deriving (Typeable, Data)
type AbsTyADat = ([Variance], [Either TyVar Q], TyDecA)

data ModExp i = MeStrC Bool [Decl i]
              | MeStrA Bool [Decl i]
              | MeName QUid
  deriving (Typeable, Data)

data Expr i w = Expr {
                  eloc_ :: Loc,
                  fv_   :: FV,
                  expr_ :: Expr' i w
                }
  deriving (Typeable, Data)
type FV        = M.Map QLid Integer
data Expr' i w = ExId Ident
               | ExStr String
               | ExInt Integer
               | ExFloat Double
               | ExCase (Expr i w) [(Patt, Expr i w)]
               | ExLetRec [Binding i w] (Expr i w)
               | ExLetDecl (Decl i) (Expr i w)
               | ExPair (Expr i w) (Expr i w)
               | ExAbs Patt (Type i w) (Expr i w)
               | ExApp (Expr i w) (Expr i w)
               | ExTAbs TyVar (Expr i w)
               | ExTApp (Expr i w) (Type i w)
               | ExPack (Type i w) (Type i w) (Expr i w)
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
          | PaPack TyVar Patt
  deriving (Typeable, Data)

type ExprT    = Expr TyTag
type TypeT    = Type TyTag
type DeclT    = Decl TyTag
type LetT     = Let TyTag
type ModExpT  = ModExp TyTag
type BindingT = Binding TyTag
type ProgT    = Prog TyTag

fv :: Expr i w -> FV
fv  = fv_

pv :: Patt -> S.Set QLid
pv PaWild             = S.empty
pv (PaVar x)          = S.singleton (J [] x)
pv (PaCon _ Nothing)  = S.empty
pv (PaCon _ (Just x)) = pv x
pv (PaPair x y)       = pv x `S.union` pv y
pv (PaStr _)          = S.empty
pv (PaInt _)          = S.empty
pv (PaAs x y)         = pv x `S.union` S.singleton (J [] y)
pv (PaPack _ x)       = pv x

exStr :: String -> Expr i w
exStr  = Expr bogus M.empty . ExStr

exInt :: Integer -> Expr i w
exInt  = Expr bogus M.empty . ExInt

exFloat :: Double -> Expr i w
exFloat  = Expr bogus M.empty . ExFloat

exCase  :: Expr i w -> [(Patt, Expr i w)] -> Expr i w
exCase e clauses = Expr {
  eloc_  = getLoc (e, map snd clauses),
  fv_    = fv e |*|
           foldl (|+|) M.empty [ fv ex |--| pv x | (x, ex) <- clauses ],
  expr_  = ExCase e clauses
}

exLetRec :: [Binding i w] -> Expr i w -> Expr i w
exLetRec bs e2 = Expr {
  eloc_  = getLoc (bs, e2),
  fv_    = let es  = map bnexpr bs
               vs  = map (J [] . bnvar) bs
               pot = foldr (|*|) (fv e2) (map fv es)
           in foldl (|-|) pot vs,
  expr_  = ExLetRec bs e2
}

exLetDecl :: Decl i -> Expr i w -> Expr i w
exLetDecl d e2 = Expr {
  eloc_  = getLoc (d, e2),
  fv_    = fv e2, -- conservative approximation
  expr_  = ExLetDecl d e2
}

exId :: Ident -> Expr i w
exId x = Expr {
  eloc_  = bogus,
  fv_    = case view x of
             Left y -> M.singleton y 1
             _      -> M.empty,
  expr_  = ExId x
}

exPair :: Expr i w -> Expr i w -> Expr i w
exPair e1 e2 = Expr {
  eloc_  = getLoc (e1, e2),
  fv_    = fv e1 |*| fv e2,
  expr_  = ExPair e1 e2
}

exAbs :: Patt -> Type i w -> Expr i w -> Expr i w
exAbs x t e = Expr {
  eloc_  = getLoc e,
  fv_    = fv e |--| pv x,
  expr_  = ExAbs x t e
}

exApp :: Expr i w -> Expr i w -> Expr i w
exApp e1 e2 = Expr {
  eloc_  = getLoc (e1, e2),
  fv_    = fv e1 |*| fv e2,
  expr_  = ExApp e1 e2
}

exTAbs :: TyVar -> Expr i w -> Expr i w
exTAbs tv e = Expr {
  eloc_  = getLoc e,
  fv_    = fv e,
  expr_  = ExTAbs tv e
}

exTApp :: Expr i w -> Type i w -> Expr i w
exTApp e1 t2 = Expr {
  eloc_  = getLoc e1,
  fv_    = fv e1,
  expr_  = ExTApp e1 t2
}

exPack :: Type i w -> Type i w -> Expr i w -> Expr i w
exPack t1 t2 e = Expr {
  eloc_  = getLoc e,
  fv_    = fv e,
  expr_  = ExPack t1 t2 e
}

exCast :: Expr i w -> Type i w -> Type i A -> Expr i w
exCast e t1 t2 = Expr {
  eloc_  = getLoc e,
  fv_    = fv e,
  expr_  = ExCast e t1 t2
}

exVar :: QLid -> Expr i w
exVar  = exId . fmap Var

exCon :: QUid -> Expr i w
exCon  = exId . fmap Con

exBVar :: Lid -> Expr i w
exBVar  = exId . J [] . Var

exBCon :: Uid -> Expr i w
exBCon  = exId . J [] . Con

exLet :: Patt -> Expr i w -> Expr i w -> Expr i w
exLet x e1 e2 = exCase e1 [(x, e2)]

exSeq :: Expr i w -> Expr i w -> Expr i w
exSeq e1 e2 = exCase e1 [(PaWild, e2)]

qlid :: String -> QLid
qlid s = case reverse (splitBy (=='.') s) of
           []   -> J [] (Lid "")
           x:xs -> J (map Uid (reverse xs)) (Lid x)

quid :: String -> QUid
quid s = case reverse (splitBy (=='.') s) of
           []   -> J [] (Uid "")
           x:xs -> J (map Uid (reverse xs)) (Uid x)

(|*|), (|+|) :: FV -> FV -> FV
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: FV -> QLid -> FV
(|-|)  = flip M.delete

(|--|) :: FV -> S.Set QLid -> FV
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
   gfoldl k z (TyQu u a b)  = z TyQu  `k` u `k` a `k` b
   gfoldl k z (TyMu a b)    = z TyMu  `k` a `k` b
   gfoldl k z (TyC a)       = z TyC   `k` a
   gfoldl k z (TyA a)       = z TyA   `k` a

   gunfold k z c = case constrIndex c of
                       1 -> k $ k $ k $ z TyCon
                       2 -> k $ z TyVar
                       3 -> k $ k $ k $ z TyQu
                       4 -> k $ k $ z TyMu
                       5 -> k $ z unTyC
                       6 -> k $ z unTyA
                       _ -> error "gunfold(Type): bad constrIndex"

   toConstr (TyCon _ _ _) = con_TyCon
   toConstr (TyVar _)     = con_TyVar
   toConstr (TyQu _ _ _)  = con_TyQu
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

con_TyCon, con_TyVar, con_TyQu, con_TyMu, con_TyC, con_TyA
        :: Constr
ty_Type :: DataType
con_TyCon = mkConstr ty_Type "TyCon" [] Prefix
con_TyVar = mkConstr ty_Type "TyVar" [] Prefix
con_TyQu  = mkConstr ty_Type "TyQu"  [] Prefix
con_TyMu  = mkConstr ty_Type "TyMu"  [] Prefix
con_TyC   = mkConstr ty_Type "TyC"   [] Prefix
con_TyA   = mkConstr ty_Type "TyA"   [] Prefix
ty_Type = mkDataType "Syntax.Type"
            [ con_TyCon, con_TyVar, con_TyQu, con_TyMu, con_TyC, con_TyA ]

instance (Ord p, (:>:) k k') =>
         (:>:) (Path p k) k'  where liftKey = J [] . liftKey
instance (:>:) BIdent Lid     where liftKey = Var
instance (:>:) BIdent Uid     where liftKey = Con

instance Eq TyTag where
  td == td' = ttId td == ttId td'

data TypeTW = TypeTC (TypeT C)
            | TypeTA (TypeT A)

typeTW :: Language w => TypeT w -> TypeTW
typeTW t = langCase t TypeTC TypeTA

instance Viewable (Path Uid BIdent) where
  type View Ident = Either QLid QUid
  view (J p (Var n)) = Left (J p n)
  view (J p (Con n)) = Right (J p n)

instance Viewable (Expr i w) where
  type View (Expr i w) = Expr' i w
  view = expr_

instance Locatable (Expr i w) where
  getLoc       = eloc_

instance Relocatable (Expr i w) where
  setLoc e loc = e { eloc_ = loc }

instance Locatable (Decl i) where
  getLoc (DcLet loc _)   = loc
  getLoc (DcTyp loc _)   = loc
  getLoc (DcAbs loc _ _) = loc
  getLoc (DcMod loc _ _) = loc
  getLoc (DcOpn loc _)   = loc
  getLoc (DcLoc loc _ _) = loc

instance Relocatable (Decl i) where
  setLoc (DcLet _ m)     loc = DcLet loc m
  setLoc (DcTyp _ td)    loc = DcTyp loc td
  setLoc (DcAbs _ at ds) loc = DcAbs loc at ds
  setLoc (DcMod _ m b)   loc = DcMod loc m b
  setLoc (DcOpn _ m)     loc = DcOpn loc m
  setLoc (DcLoc _ d d')  loc = DcLoc loc d d'

instance Locatable (Binding i w) where
  getLoc = getLoc . bnexpr

instance Eq QualSet where
  QualSet q ixs == QualSet q' ixs'
    | q == maxBound && q' == maxBound = True
    | otherwise                       = q == q' && ixs == ixs'

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
      TyQu u x t    === TyQu u' x' t'
        | u == u' && tvqual x == tvqual x' =
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
    TyQu u x t     `cmp` TyQu u' x' t' 
      | u == u' && tvqual x == tvqual x' = 
        tysubst1 x a t `chk` tysubst1 x' a t'
          where a = TyVar (freshTyVar x (ftv [t, t']))
    _            `cmp` _               = return False

instance Show Q where
  showsPrec _ Qa = ('A':)
  showsPrec _ Qu = ('U':)

instance Show (LangRep w) where
  showsPrec _ A = ('A':)
  showsPrec _ C = ('C':)

instance Show Variance where
  showsPrec _ Invariant     = ('1':)
  showsPrec _ Covariant     = ('+':)
  showsPrec _ Contravariant = ('-':)
  showsPrec _ Omnivariant   = ('0':)

instance Show QualSet where
  show (QualSet q ixs) =
    show q ++ " \\/ bigVee " ++ show (S.toList ixs)

instance Show Quant where
  show Forall = "all"
  show Exists = "ex"

instance Show Lid where
  showsPrec _ (Lid s) = case s of
    '_':_             -> (s++)
    c  :_ | isAlpha c -> (s++)
    '*':_             -> ("( "++) . (s++) . (" )"++)
    _                 -> ('(':) . (s++) . (')':)

instance Show Uid where
  show = unUid

instance Show BIdent where
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

instance Bounded QualSet where
  minBound = QualSet minBound S.empty
  maxBound = QualSet maxBound S.empty

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
        || Just y == (x \/? y)

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

instance Ord a => PO (S.Set a) where
  (\/) = S.union
  (/\) = S.intersection

instance PO QualSet where
  QualSet q ixs /\? QualSet q' ixs'
    | q == q' = return (QualSet q (ixs /\ ixs'))
  qs /\? qs'  = fail $
      "GLB " ++ show qs ++ " /\\ " ++ show qs' ++ " does not exist"
  QualSet q ixs \/ QualSet q' ixs'
    | q == maxBound  = QualSet maxBound S.empty
    | q' == maxBound = QualSet maxBound S.empty
    | otherwise      = QualSet (q \/ q') (ixs \/ ixs')

  -- Special cases for dual session types:
instance  PO (Type TyTag A) where
  ifMJ bi t1i t2i = clean `liftM` chk [] bi t1i t2i where
    clean :: TypeT w -> TypeT w
    clean (TyCon c ps td)  = TyCon c (map clean ps) td
    clean (TyVar a)        = TyVar a
    clean (TyQu u a t)     = TyQu u a (clean t)
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
                              then TyCon (qlid "-o") ps0 tdLol
                              else TyCon (qlid "->") ps0 tdArr
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
    cmp seen b (TyQu u a t) (TyQu u' a' t') | u == u' = do
      qual <- ifMJ (not b) (tvqual a) (tvqual a')
      let a1  = a { tvqual = qual } `freshTyVar` (ftv [t, t'])
          t1  = tysubst1 a (TyVar a1) t
          t'1 = tysubst1 a' (TyVar a1) t'
      TyQu u a1 `liftM` chk seen b t1 t'1
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
class Data w => Language' w where
  type OtherLang w
  reifyLang   :: LangRep w
  langCase    :: f w -> (w ~ C => f C -> r) -> (w ~ A => f A -> r) -> r
  langMapType :: Functor f =>
                 (forall w'. Language w' => f (Type td w')) -> f (Type td w)

instance Language' C where
  type OtherLang C = A
  reifyLang        = C
  langCase x fc _  = fc x
  langMapType x    = fmap tyA x

instance Language' A where
  type OtherLang A = C
  reifyLang        = A
  langCase x _ fa  = fa x
  langMapType x    = fmap tyC x

type SameLang w = OtherLang (OtherLang w)

class (Language' (OtherLang w), Language' w) => Language w
instance Language C
instance Language A

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
  ftv (TyQu _ tv t)  = M.delete tv (ftv t)
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
  ts (TyQu u a' t')
                = sameLang t' t
                    (\_ _ ->
                      if a' == a
                        then TyQu u a' t'
                        else
                          let a'' = freshTyVar a' (ftv [t, t'])
                           in TyQu u a'' (ts (tysubst1 a' (TyVar a'') t')))
                    (TyQu u a' (ts t'))
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
  d (TyCon (J [] (Lid "->"))
       [TyCon (J [] (Lid "send")) [ta] _, tr] _)
    = TyCon (qlid "->") [TyCon (qlid "recv") [ta] tdRecv, d tr] tdArr
  d (TyCon (J [] (Lid "->"))
       [TyCon (J [] (Lid "recv")) [ta] _, tr] _)
    = TyCon (qlid "->") [TyCon (qlid "send") [ta] tdSend, d tr] tdArr
  d (TyCon (J [] (Lid "select"))
       [TyCon (J [] (Lid "*")) [t1, t2] _] _)
    = TyCon (qlid "follow") [TyCon (qlid "*") [d t1, d t2] tdTuple] tdFollow
  d (TyCon (J [] (Lid "follow"))
       [TyCon (J [] (Lid "*")) [t1, t2] _] _)
    = TyCon (qlid "select") [TyCon (qlid "*") [d t1, d t2] tdTuple] tdSelect
  d (TyMu tv t)
    = TyMu tv (d t)
  d t = t

qsConst :: Q -> QualSet
qsConst  = flip QualSet S.empty

qsVar   :: Int -> QualSet
qsVar    = qsVars . return

qsVars  :: [Int] -> QualSet
qsVars   = QualSet minBound . S.fromList

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
  = Right q : [ Left (tvs !! ix) | ix <- S.toList ixs ]

tdUnit, tdBool, tdInt, tdFloat, tdString,
  tdArr, tdLol, tdTuple :: TyTag

tdUnit       = TyTag (-1)  []          minBound          True
tdBool       = TyTag (-2)  []          minBound          True
tdInt        = TyTag (-3)  []          minBound          True
tdFloat      = TyTag (-4)  []          minBound          True
tdString     = TyTag (-5)  []          minBound          True
tdArr        = TyTag (-6)  [-1, 1]     minBound          False
tdLol        = TyTag (-7)  [-1, 1]     maxBound          False
tdTuple      = TyTag (-8)  [1, 1]      qualSet           True
  where qualSet = QualSet minBound (S.fromList [0, 1])

tdDual, tdSend, tdRecv, tdSelect, tdFollow :: TyTag
-- For session types:
tdDual       = TyTag (-11) [-1] minBound          False
tdSend       = TyTag (-12) [1]  minBound          False
tdRecv       = TyTag (-13) [-1] minBound          False
tdSelect     = TyTag (-14) [1]  minBound          False
tdFollow     = TyTag (-15) [1]  minBound          False

tyGround      :: String -> Type () w
tyGround s     = TyCon (qlid s) [] ()

tyArr         :: Type () w -> Type () w -> Type () w
tyArr a b      = TyCon (qlid "->") [a, b] ()

tyLol         :: Type () w -> Type () w -> Type () w
tyLol a b      = TyCon (qlid "-o") [a, b] ()

tyTuple       :: Type () w -> Type () w -> Type () w
tyTuple a b    = TyCon (qlid "*") [a, b] ()

tyUnitT        :: TypeT w
tyUnitT         = TyCon (qlid "unit") [] tdUnit

tyBoolT        :: TypeT w
tyBoolT         = TyCon (qlid "bool") [] tdBool

tyArrT         :: TypeT w -> TypeT w -> TypeT w
tyArrT a b      = TyCon (qlid "->") [a, b] tdArr

tyLolT         :: TypeT w -> TypeT w -> TypeT w
tyLolT a b      = TyCon (qlid "-o") [a, b] tdLol

tyTupleT       :: TypeT w -> TypeT w -> TypeT w
tyTupleT a b    = TyCon (qlid "*") [a, b] tdTuple

infixr 8 `tyArrT`, `tyLolT`
infixl 7 `tyTupleT`

qualifier     :: TypeT A -> Q
qualifier (TyCon _ ps td) = bigVee qs' where
  qs  = map qualifier ps
  qs' = q : map (qs !!) (S.toList ixs)
  QualSet q ixs = ttQual td
qualifier (TyVar (TV _ q))   = q
qualifier (TyQu _ _ t)       = qualifier t
qualifier (TyMu _ t)         = qualifier t
qualifier _                  = Qu

-- Funtional types
funtypes    :: [TyTag]
funtypes     = [tdArr, tdLol]

cgetas :: Type i C -> [Type i A]
cgetas (TyCon _ ts _) = concatMap cgetas ts
cgetas (TyVar _)      = []
cgetas (TyQu _ _ t)   = cgetas t
cgetas (TyMu _ t)     = cgetas t
cgetas (TyA t)        = [t]
cgetas _              = [] -- can't happen

agetcs :: Type i A -> [Type i C]
agetcs (TyCon _ ts _) = concatMap agetcs ts
agetcs (TyVar _)      = []
agetcs (TyQu _ _ t)   = agetcs t
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
  = TyCon (qlid "->") [ctype2atype td, ctype2atype tr] tdArr
ctype2atype (TyQu u tv t)
                      = TyQu u tv' (ctype2atype t')
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
  = TyCon (qlid "->") [atype2ctype td, atype2ctype tr] tdArr
atype2ctype (TyQu u tv t)
                      = TyQu u tv' (atype2ctype t')
                        where t' = tysubst tv (tyC (TyVar tv')) t
                              tv' = tv { tvqual = Qu } `freshTyVar` ftv t
atype2ctype (TyMu tv t)
                      = TyMu tv' (atype2ctype t')
                        where t' = tysubst tv (tyC (TyVar tv')) t
                              tv' = tv { tvqual = Qu } `freshTyVar` ftv t
atype2ctype t         = tyA t

syntacticValue :: Expr i w -> Bool
syntacticValue e = case view e of
  ExId _       -> True
  ExStr _      -> True
  ExInt _      -> True
  ExPair e1 e2 -> syntacticValue e1 && syntacticValue e2
  ExAbs _ _ _  -> True
  ExApp e1 e2  -> syntacticConstructor e1 && syntacticValue e2
  ExTAbs _ _   -> True
  ExTApp e1 _  -> syntacticValue e1
  _            -> False

syntacticConstructor :: Expr i w -> Bool
syntacticConstructor e = case view e of
  ExId (J [] (Con _)) -> True
  ExTApp e1 _         -> syntacticConstructor e1
  ExApp e1 e2         -> syntacticConstructor e1 && syntacticValue e2
  _                   -> False

castableType :: TypeT w -> Bool
castableType (TyVar _)      = False
castableType (TyCon _ _ td) = td `elem` funtypes
castableType (TyQu _ _ t)   = castableType t
castableType (TyMu _ t)     = castableType t
castableType (TyC _)        = False
castableType (TyA _)        = False

letName :: Let i -> Lid
letName (LtA _ x _ _)   = x
letName (LtC _ x _ _)   = x
letName (LtInt _ x _ _) = x

prog2decls :: Prog i -> [Decl i]
prog2decls (Prog ds (Just e))
  = ds ++ [DcLet (getLoc e) (LtC True (Lid "it") Nothing e)]
prog2decls (Prog ds Nothing)
  = ds

-- Unfolding various sequences

unfoldExAbs :: Expr i w -> ([Either (Patt, Type i w) TyVar], Expr i w)
unfoldExAbs  = unscanr each where
  each e = case view e of
    ExAbs x t e' -> Just (Left (x, t), e')
    ExTAbs tv e' -> Just (Right tv, e')
    _            -> Nothing

unfoldTyQu  :: Quant -> Type i w -> ([TyVar], Type i w)
unfoldTyQu u = unscanr each where
  each (TyQu u' x t) | u == u' = Just (x, t)
  each _                       = Nothing

unfoldExTApp :: Expr i w -> ([Type i w], Expr i w)
unfoldExTApp  = unscanl each where
  each e = case view e of
    ExTApp e' t  -> Just (t, e')
    _            -> Nothing

unfoldExApp :: Expr i w -> ([Expr i w], Expr i w)
unfoldExApp  = unscanl each where
  each e = case view e of
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
    TyQu u a t -> do
      print $ show u ++ " " ++ show a ++ ". {"
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
