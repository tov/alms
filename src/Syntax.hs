-----------------------------------------------------------------------------
-- |
-- This module provides syntax and basic syntax operations for
-- the implementation of the language from the paper "Stateful Contracts
-- for Affine Types".
--
-----------------------------------------------------------------------------

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
  -- * Languages, variances, qualifiers
  -- ** Languages
  -- |
  -- We have two sublanguages, A for affine and C for conventional
  Language, A, C, Language'(..), SameLang, LangRep(..), LangRepMono(..),
  -- ** Variances
  Variance(..),
  -- ** Qualifiers
  Q(..), QualSet,
  -- *** Qualifier operations
  qsConst, qsVar, qsVars, qsFromListM, qsFromList, qsToList,

  -- * Identifiers
  Path(..),
  Lid(..), Uid(..), BIdent(..),
  Ident, QLid, QUid,
  TyVar(..),
  qlid, quid,

  -- * Types
  TyTag(..),
  Quant(..),
  Type(..),
  TypeT,
  TypeTW(..), typeTW,
  -- * Synthetic constructors
  tyC, tyA, tyAll, tyEx,
  -- ** Accessors and updaters
  tycon, tyargs, tyinfo,
  setTycon, setTyinfo,
  -- ** Freshness
  Ftv(..), freshTyVar, freshTyVars,
  -- ** Substitutions
  tysubst, tysubst1,
  -- ** Queries and conversions
  qualifier, transparent, funtypes, castableType,
  ctype2atype, atype2ctype, cgetas, agetcs,
  replaceTyTags, removeTyTags,

  -- * Programs and declarations
  Prog(..), ProgT,
  Decl(..), DeclT,
  Let(..), LetT,
  TyDec(..), TyDecC(..), TyDecA(..),
  AbsTy(..),
  ModExp(..), ModExpT,
  ExnDec(..),
  -- ** Synthetic consructors
  -- | These fill in the source location fields with a bogus location
  dcLet, dcTyp, dcAbs, dcMod, dcOpn, dcLoc, dcExn,
  -- ** Operations
  letName, prog2decls,

  -- * Exceptions
  ExnId(..),
  -- ** Built-in exceptions
  eiIOError, eiBlame, eiPatternMatch,

  -- * Expressions
  Expr(), ExprT, Expr'(..),
  -- ** Two-level expression constructors
  -- | These fill in the source location field based on the
  -- subexpressions and perform the free variable analysis
  exId, exStr, exInt, exFloat, exCase, exLetRec, exLetDecl, exPair,
  exAbs, exApp, exTAbs, exTApp, exPack, exCast,
  -- ** Synthetic expression constructors
  exVar, exCon, exBVar, exBCon, exLet, exSeq,
  -- ** Expression accessors and updaters
  fv, exprType, (*:*), setExnId, getExnId, (*<*),
  syntacticValue,

  -- * Patterns and bindings
  Binding(..), BindingT, Patt(..),
  pv,

  -- * Partial orders
  PO(..), bigVee, bigVeeM, bigWedge, bigWedgeM,

  -- * Built-in types
  -- ** Type information
  tdUnit, tdInt, tdFloat, tdString, tdExn, tdTuple, tdArr, tdLol,
  -- ** Session types
  dualSessionType,
  tdDual, tdSend, tdRecv, tdSelect, tdFollow,
  -- ** Convenience type constructors
  tyGround, tyArr, tyLol, tyTuple,
  tyUnitT, tyArrT, tyLolT, tyTupleT, tyExnT,

  -- * Unfold syntax to lists
  unfoldExAbs, unfoldTyQu, unfoldExTApp, unfoldExApp, unfoldTyFun,

  -- * Miscellany
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

-- LANGUAGES, QUALIFIERS, VARIANCES

-- | The affine language
data A deriving Typeable
-- | The conventional language
data C deriving Typeable

-- | GADT for run-time language representation
data LangRep w where
  A :: LangRep A
  C :: LangRep C

-- | Non-GADT language representation
data LangRepMono = LC | LA
  deriving (Eq, Typeable, Data, Show, Ord)

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
data QualSet = QualSet Q (S.Set Int)
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

-- IDENTIFIERS

-- | lowercase identifiers (variables, tycons)
newtype Lid = Lid { unLid :: String }
  deriving (Eq, Ord, Typeable, Data)

-- | uppercase identifiers (modules, datacons)
newtype Uid = Uid { unUid :: String }
  deriving (Eq, Ord, Typeable, Data)

-- | bare (unqualified) identifers
data BIdent = Var { unVar :: Lid }
            | Con { unCon :: Uid }
  deriving (Eq, Ord, Typeable, Data)

-- | path-qualified uppercase identifiers
type QUid  = Path Uid Uid
-- | path-qualified lowecase identifiers
type QLid  = Path Uid Lid
-- | path-qualified identifiers
type Ident = Path Uid BIdent

-- | Type variables include qualifiers
data TyVar = TV { tvname :: Lid, tvqual :: Q }
  deriving (Eq, Ord, Typeable, Data)

-- | Info about a type constructor (for language A)
data TyTag =
  TyTag {
    -- Identity
    ttId    :: Integer,
    -- The variance of each of its parameters
    ttArity :: [Variance],
    -- Determines qualifier as above
    ttQual  :: QualSet,
    -- transparent?
    ttTrans :: Bool,
    -- upper qualifier bounds for parameters
    ttBound :: [Q]
  }
  deriving (Show, Typeable, Data)

-- | Types are parameterized by:
--
--   [@i@] the type of information associated with each tycon
--   [@w@] the sublanguage, A or C
data Type i w where
  TyCon :: QLid -> [Type i w] -> i -> Type i w
  TyVar :: TyVar -> Type i w
  TyQu  :: Quant -> TyVar -> Type i w -> Type i w
  TyMu  :: TyVar -> Type i w -> Type i w
  TyC   :: Type i C -> Type i A
  TyA   :: Type i A -> Type i C
  deriving Typeable

-- | Type quantifers
data Quant = Forall | Exists
  deriving (Typeable, Data, Eq)

tycon :: Type i w -> QLid
tycon (TyCon tc _ _)  = tc
tycon _               = error "tycon: not a TyCon"
tyargs :: Type i w -> [Type i w]
tyargs (TyCon _ ts _) = ts
tyargs _              = error "tyargs: not a TyCon"
tyinfo :: Type i w -> i
tyinfo (TyCon _ _ i)  = i
tyinfo _              = error "tyinfo: not a TyCon"

setTycon :: Type i w -> QLid -> Type i w
setTycon (TyCon _ ts i) tc = TyCon tc ts i
setTycon t _               = t
setTyinfo :: Type i w -> i -> Type i w
setTyinfo (TyCon tc ts _) i = TyCon tc ts i
setTyinfo t _               = t

infixl `setTycon`, `setTyinfo`

-- | Synthetic constructors for wrapper (interlanguage) types
-- prevent multiple nested wrapping.  Essentially we make the
-- type algebra less free by adding constrants:
--
-- @
--    tyC (tyA t) = t
--    tyA (tyC t) = t
-- @
tyC :: Type i C -> Type i A
tyC (TyA t) = t
tyC t       = TyC t

tyA :: Type i A -> Type i C
tyA (TyC t) = t
tyA t       = TyA t

-- | Convenience constructors for qualified types
tyAll, tyEx :: TyVar -> Type i w -> Type i w
tyAll = TyQu Forall
tyEx  = TyQu Exists

-- | Remove tycon information from a type
removeTyTags :: Type i w -> Type () w
removeTyTags  = untype where
  untype :: Type i w -> Type () w
  untype (TyCon con args _) = TyCon con (map untype args) ()
  untype (TyVar tv)         = TyVar tv
  untype (TyQu quant tv t)  = TyQu quant tv (untype t)
  untype (TyMu tv t)        = TyMu tv (untype t)
  untype (TyC t)            = TyC (untype t)
  untype (TyA t)            = TyA (untype t)

-- | A program is a sequence of declarations, maybe followed by a C
-- expression
data Prog i = Prog [Decl i] (Maybe (Expr i C))
  deriving (Typeable, Data)

-- | Declarations
data Decl i
  -- | Constant declaration
  = DcLet Loc (Let i)
  -- | Type declaration
  | DcTyp Loc TyDec
  -- | Abstype block declaration
  | DcAbs Loc AbsTy [Decl i]
  -- | Module declaration
  | DcMod Loc Uid (ModExp i)
  -- | Module open
  | DcOpn Loc (ModExp i)
  -- | Local block
  | DcLoc Loc [Decl i] [Decl i]
  -- | Exception declaration
  | DcExn Loc ExnDec
  deriving (Typeable, Data)

-- | Build a constant declaration with bogus source location
dcLet :: Let i -> Decl i
dcLet  = DcLet bogus

-- | Build a type declaration with bogus source location
dcTyp :: TyDec -> Decl i
dcTyp  = DcTyp bogus

-- | Build a abstype declaration with bogus source location
dcAbs :: AbsTy -> [Decl i] -> Decl i
dcAbs  = DcAbs bogus

-- | Build a module with bogus source location
dcMod :: Uid -> ModExp i -> Decl i
dcMod  = DcMod bogus

-- | Build an open declaration with bogus source location
dcOpn :: ModExp i -> Decl i
dcOpn  = DcOpn bogus

-- | Build local block with bogus source location
dcLoc :: [Decl i] -> [Decl i] -> Decl i
dcLoc  = DcLoc bogus

-- | Build an exception declaration with bogus source location
dcExn :: ExnDec -> Decl i
dcExn  = DcExn bogus

-- | Constant declarations (@let@)
data Let i
  -- | An affine-language constant
  = LtA Bool Lid (Maybe (Type i A)) (Expr i A)
  -- | A conventional-language constant
  | LtC Bool Lid (Maybe (Type i C)) (Expr i C)
  -- | An affine-to-conventional interface
  | LtInt Bool Lid (Type i A) QLid
  deriving (Typeable, Data)

-- | Type declarations (@type@)
data TyDec
  -- | An affine-language type (or mutually recursive types)
  = TyDecC Bool [TyDecC]
  -- | An conventional-language type (or mutually recursive types)
  | TyDecA Bool [TyDecA]
  -- | A transparent (both languages) type (or mutually recursive types)
  | TyDecT [TyDecA]
  deriving (Typeable, Data)

-- | Affine language type declarations
data TyDecC
  -- | An abstract (empty) type
  = TdAbsC {
    tdcName      :: Lid,
    tdcParams    :: [TyVar]
  }
  -- | A type synonym
  | TdSynC {
    tdcName      :: Lid,
    tdcParams    :: [TyVar],
    tdcRHS       :: Type () C
  }
  -- | An algebraic datatype
  | TdDatC {
    tdcName      :: Lid,
    tdcParams    :: [TyVar],
    tdcAlts      :: [(Uid, Maybe (Type () C))]
  }
  deriving (Typeable, Data)

-- | Affine language type declarations
data TyDecA
  -- | An abstract (empty) type
  = TdAbsA {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    -- | The variance of each parameter
    tdaVariances :: [Variance],
    -- | Whether each parameter contributes to the qualifier
    tdaQual      :: [Either TyVar Q]
  }
  -- | A type synonym
  | TdSynA {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    tdaRHS       :: Type () A
  }
  -- | An algebraic datatype
  | TdDatA {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    tdaAlts      :: [(Uid, Maybe (Type () A))]
  }
  deriving (Typeable, Data)

-- | An abstype block
data AbsTy   = AbsTyC {
                 atTopLevel    :: Bool,
                 atTyDecC      :: [TyDecC]
               }
             | AbsTyA {
                 atTopLevel    :: Bool,
                 atTyDecA      :: [AbsTyADat]
               }
  deriving (Typeable, Data)
-- | An abstract type in language A needs to specify variances
-- and the qualifier
type AbsTyADat = ([Variance], [Either TyVar Q], TyDecA)

-- | A module expression
data ModExp i
  -- | A language C module literal
  = MeStrC Bool [Decl i]
  -- | A language A module literal
  | MeStrA Bool [Decl i]
  -- | A module variable
  | MeName QUid
  deriving (Typeable, Data)

-- | Exception declarations
data ExnDec   = ExnC {
                  exnToplevel :: Bool,
                  exnName     :: Uid,
                  exnCField   :: Maybe (Type () C)
                }
              | ExnA {
                  exnToplevel :: Bool,
                  exnName     :: Uid,
                  exnAField   :: Maybe (Type () A)
                }
  deriving (Typeable, Data)

-- | Expressions are a two-level type, which simulates a sort
-- of inheritance without losing pattern matching.  Every expression
-- has several fields in addition to its particular abstract syntax.
data Expr i w
  = Expr {
      -- | source location
      eloc_  :: Loc,
      -- | free variables
      fv_    :: FV,
      -- | possibly its type (used for translation)
      type_  :: Maybe (Either (TypeT C) (TypeT A)),
      -- | if it's an exception constructor, its identity
      exnid_ :: Maybe ExnId,
      -- | the underlying sum type
      expr_  :: Expr' i w
    }
  deriving (Typeable, Data)

-- | The underlying expression type, which we can pattern match without
-- dealing with the common fields above.
data Expr' i w
  -- | variables and datacons
  = ExId Ident
  -- | string literals
  | ExStr String
  -- | integer literals
  | ExInt Integer
  -- | floating point literals
  | ExFloat Double
  -- | case expressions (including desugared @if@ and @let@)
  | ExCase (Expr i w) [(Patt, Expr i w)]
  -- | recursive let expressions
  | ExLetRec [Binding i w] (Expr i w)
  -- | nested declarations
  | ExLetDecl (Decl i) (Expr i w)
  -- | pair construction
  | ExPair (Expr i w) (Expr i w)
  -- | lambda
  | ExAbs Patt (Type i w) (Expr i w)
  -- | application
  | ExApp (Expr i w) (Expr i w)
  -- | type abstraction
  | ExTAbs TyVar (Expr i w)
  -- | type application
  | ExTApp (Expr i w) (Type i w)
  -- | existential construction
  | ExPack (Maybe (Type i w)) (Type i w) (Expr i w)
  -- | dynamic promotion
  | ExCast (Expr i w) (Maybe (Type i w)) (Type i A)
  deriving (Typeable, Data)

-- | Our free variables function returns not merely a set,
-- but a map from names to a count of maximum occurrences.
type FV        = M.Map QLid Integer

-- | Exceptions need identity beyond their names, since one
-- exception declaration can shadow another, and we need to catch
-- only the right ones a run time.
data ExnId     = ExnId {
                   eiIndex :: Integer,
                   eiName  :: Uid,
                   eiLang  :: LangRepMono
                 }
  deriving (Eq, Show, Typeable, Data)

-- | Let-rec bindings require us to give types
data Binding i w = Binding {
  bnvar  :: Lid,
  bntype :: Type i w,
  bnexpr :: Expr i w
}
  deriving (Typeable, Data)

-- | Patterns
data Patt
  -- | wildcard
  = PaWild
  -- | variable pattern
  | PaVar Lid
  -- | datacon, possibly with parameter, possibly an exception
  | PaCon Uid (Maybe Patt) (Maybe ExnId)
  -- | pair pattern
  | PaPair Patt Patt
  -- | string literal
  | PaStr String
  -- | integer literal
  | PaInt Integer
  -- | bind an identifer and a pattern (@as@)
  | PaAs Patt Lid
  -- | existential opening
  | PaPack TyVar Patt
  deriving (Typeable, Data)

-- | A type-checked expression (has tycon info)
type ExprT    = Expr TyTag
-- | A type-checked type (has tycon info)
type TypeT    = Type TyTag
-- | A type-checked declaration (has tycon info)
type DeclT    = Decl TyTag
-- | A type-checked constant declaration (has tycon info)
type LetT     = Let TyTag
-- | A type-checked module expression (has tycon info)
type ModExpT  = ModExp TyTag
-- | A type-checked let-rec binding (has tycon info)
type BindingT = Binding TyTag
-- | A type-checked program (has tycon info)
type ProgT    = Prog TyTag

-- | Accessor for the free variables field of expressions
fv :: Expr i w -> FV
fv  = fv_

-- | Get the type of an expression, if known
exprType :: Expr i w -> Maybe (Either (TypeT C) (TypeT A))
exprType  = type_

-- | Update the type of an expression
(*:*) :: Language w' => ExprT w -> TypeT w' -> ExprT w
e *:* t = e {
  type_ = Just (langCase t Left Right)
}

-- | Get the exception id of an expression
getExnId :: Expr i w -> Maybe ExnId
getExnId  = exnid_

-- | Update the exception id of an expression
setExnId :: Expr i w -> Maybe ExnId -> Expr i w
setExnId e mz = e { exnid_ = mz }

-- | Clone the type and exception id from the right expression
-- onto the left expression
(*<*) :: Expr i w -> Expr i w' -> Expr i w
e *<* e' = e { type_ = type_ e', exnid_ = exnid_ e' }

-- | The set of variables bound by a pattern
pv :: Patt -> S.Set Lid
pv PaWild               = S.empty
pv (PaVar x)            = S.singleton x
pv (PaCon _ Nothing _)  = S.empty
pv (PaCon _ (Just x) _) = pv x
pv (PaPair x y)         = pv x `S.union` pv y
pv (PaStr _)            = S.empty
pv (PaInt _)            = S.empty
pv (PaAs x y)           = pv x `S.union` S.singleton y
pv (PaPack _ x)         = pv x

expr0 :: Expr i w
expr0  = Expr {
  eloc_  = bogus,
  fv_    = M.empty,
  type_  = Nothing,
  exnid_ = Nothing,
  expr_  = undefined
}

mkexpr0   :: Expr' i w -> Expr i w
mkexpr0 e' = expr0 { expr_  = e' }

exStr :: String -> Expr i w
exStr  = mkexpr0 . ExStr

exInt :: Integer -> Expr i w
exInt  = mkexpr0 . ExInt

exFloat :: Double -> Expr i w
exFloat  = mkexpr0 . ExFloat

exCase  :: Expr i w -> [(Patt, Expr i w)] -> Expr i w
exCase e clauses = expr0 {
  eloc_  = getLoc (e, map snd clauses),
  fv_    = fv e |*|
           foldl (|+|) M.empty [ fv ex |--| pv x | (x, ex) <- clauses ],
  expr_  = ExCase e clauses
}

exLetRec :: [Binding i w] -> Expr i w -> Expr i w
exLetRec bs e2 = expr0 {
  eloc_  = getLoc (bs, e2),
  fv_    = let es  = map bnexpr bs
               vs  = map (J [] . bnvar) bs
               pot = foldr (|*|) (fv e2) (map fv es)
           in foldl (|-|) pot vs,
  expr_  = ExLetRec bs e2
}

exLetDecl :: Decl i -> Expr i w -> Expr i w
exLetDecl d e2 = expr0 {
  eloc_  = getLoc (d, e2),
  fv_    = fv e2, -- conservative approximation
  expr_  = ExLetDecl d e2
}

exId :: Ident -> Expr i w
exId x = expr0 {
  fv_    = case view x of
             Left y -> M.singleton y 1
             _      -> M.empty,
  expr_  = ExId x
}

exPair :: Expr i w -> Expr i w -> Expr i w
exPair e1 e2 = expr0 {
  eloc_  = getLoc (e1, e2),
  fv_    = fv e1 |*| fv e2,
  expr_  = ExPair e1 e2
}

exAbs :: Patt -> Type i w -> Expr i w -> Expr i w
exAbs x t e = expr0 {
  eloc_  = getLoc e,
  fv_    = fv e |--| pv x,
  expr_  = ExAbs x t e
}

exApp :: Expr i w -> Expr i w -> Expr i w
exApp e1 e2 = expr0 {
  eloc_  = getLoc (e1, e2),
  fv_    = fv e1 |*| fv e2,
  expr_  = ExApp e1 e2
}

exTAbs :: TyVar -> Expr i w -> Expr i w
exTAbs tv e = expr0 {
  eloc_  = getLoc e,
  fv_    = fv e,
  expr_  = ExTAbs tv e
}

exTApp :: Expr i w -> Type i w -> Expr i w
exTApp e1 t2 = expr0 {
  eloc_  = getLoc e1,
  fv_    = fv e1,
  expr_  = ExTApp e1 t2
}

exPack :: Maybe (Type i w) -> Type i w -> Expr i w -> Expr i w
exPack t1 t2 e = expr0 {
  eloc_  = getLoc e,
  fv_    = fv e,
  expr_  = ExPack t1 t2 e
}

exCast :: Expr i w -> Maybe (Type i w) -> Type i A -> Expr i w
exCast e t1 t2 = expr0 {
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

-- | Sugar for generating AST for qualified lowercase identifers
qlid :: String -> QLid
qlid s = case reverse (splitBy (=='.') s) of
           []   -> J [] (Lid "")
           x:xs -> J (map Uid (reverse xs)) (Lid x)

-- | Sugar for generating AST for qualified uppercase identifers
quid :: String -> QUid
quid s = case reverse (splitBy (=='.') s) of
           []   -> J [] (Uid "")
           x:xs -> J (map Uid (reverse xs)) (Uid x)

-- | Used by the free variables analysis
(|*|), (|+|) :: FV -> FV -> FV
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: FV -> QLid -> FV
(|-|)  = flip M.delete

(|--|) :: FV -> S.Set Lid -> FV
(|--|)  = S.fold (M.delete . J [])

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
  getLoc (DcExn loc _)   = loc

instance Relocatable (Decl i) where
  setLoc (DcLet _ m)     loc = DcLet loc m
  setLoc (DcTyp _ td)    loc = DcTyp loc td
  setLoc (DcAbs _ at ds) loc = DcAbs loc at ds
  setLoc (DcMod _ m b)   loc = DcMod loc m b
  setLoc (DcOpn _ m)     loc = DcOpn loc m
  setLoc (DcLoc _ d d')  loc = DcLoc loc d d'
  setLoc (DcExn _ e)     loc = DcExn loc e

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

instance PO (Type TyTag C) where
  t \/? TyQu Forall tv (TyVar tv') | tv == tv' = return t
  TyQu Forall tv (TyVar tv') \/? t | tv == tv' = return t
  t \/? t' = if t == t' then return t else fail "\\/?: does not exist"

  _ /\? t'@(TyQu Forall tv (TyVar tv')) | tv == tv' = return t'
  t'@(TyQu Forall tv (TyVar tv')) /\? _ | tv == tv' = return t'
  t /\? t' = if t == t' then return t else fail "/\\?: does not exist"

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

-- | Partial orders.
--  Minimal complete definition is one of:
--
--  * 'ifMJ'
--
--  * '(\/)', '(/\)'    (only if it's a lattice)
--
--  * '(\/?)', '(/\?)'  (partial join and meet)
class Eq a => PO a where
  -- | Takes a boolean parameter, and does join if true
  --   and meet if false.  This sometimes allows us to exploit duality
  --   to define both at once.
  ifMJ :: Monad m => Bool -> a -> a -> m a
  ifMJ True  x y = return (x \/ y)
  ifMJ False x y = return (x /\ y)

  -- | Partial join returns in a monad, in case join DNE
  (\/?) :: Monad m => a -> a -> m a
  (\/?)  = ifMJ True

  -- | Partial meet returns in a monad, in case meet DNE
  (/\?) :: Monad m => a -> a -> m a
  (/\?)  = ifMJ False

  -- | Total join
  (\/)  :: a -> a -> a
  -- | Total meet
  (/\)  :: a -> a -> a
  x \/ y = fromJust (x \/? y)
  x /\ y = fromJust (x /\? y)

  -- | The order relation (derived)
  (<:)  :: a -> a -> Bool
  x <: y = Just x == (x /\? y)
        || Just y == (x \/? y)

infixl 7 /\, /\?
infixl 6 \/, \/?
infix 4 <:

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

instance Ord a => PO (S.Set a) where
  (\/) = S.union
  (/\) = S.intersection

-- | The 'QualSet' partial order
-- (relation only defined for same-length qualsets)
instance PO QualSet where
  QualSet q ixs /\? QualSet q' ixs'
    | q == q' = return (QualSet q (ixs /\ ixs'))
  qs /\? qs'  = fail $
      "GLB " ++ show qs ++ " /\\ " ++ show qs' ++ " does not exist"
  QualSet q ixs \/ QualSet q' ixs'
    | q == maxBound  = QualSet maxBound S.empty
    | q' == maxBound = QualSet maxBound S.empty
    | otherwise      = QualSet (q \/ q') (ixs \/ ixs')

-- | The Type partial order
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

    -- Special cases to treat "all 'a. 'a" as bottom:
    cmp _ b t'@(TyQu Forall tv (TyVar tv')) t
      | tv == tv' && qualifier t <: tvqual tv = return (if b then t else t')
    cmp _ b t t'@(TyQu Forall tv (TyVar tv'))
      | tv == tv' && qualifier t <: tvqual tv = return (if b then t else t')
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

-- | In GHC 6.10, reifyLang is enough, but in 6.8, we need langCase
--   and langMapType, it seems.
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

-- | Serves as a witness that 'OtherLang' is involutive
type SameLang w = OtherLang (OtherLang w)

class (Language' (OtherLang w), Language' w) => Language w
instance Language C
instance Language A

-- | Dispatch on whether two terms are in the same language or not
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

-- | Class for getting free type variables (from types, expressions,
-- lists thereof, pairs thereof, etc.)
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

-- | Special case of type substitution forces unification of the
-- languages of its two Type arguments
tysubst1 :: Language w => TyVar -> TypeT w -> TypeT w -> TypeT w
tysubst1  = tysubst

-- | Type substitution (NB: the languages need not match, since
-- types embed in one another)
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

-- |
-- Helper for finding the dual of a session type (since we can't
-- express this directly in the type system at this point)
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

tdUnit, tdInt, tdFloat, tdString,
  tdArr, tdLol, tdExn, tdTuple :: TyTag

tdUnit       = TyTag (-1)  []          minBound  True  []
tdInt        = TyTag (-2)  []          minBound  True  []
tdFloat      = TyTag (-3)  []          minBound  True  []
tdString     = TyTag (-4)  []          minBound  True  []
tdArr        = TyTag (-5)  [-1, 1]     minBound  False [maxBound, maxBound]
tdLol        = TyTag (-6)  [-1, 1]     maxBound  False [maxBound, maxBound]
tdExn        = TyTag (-7)  []          maxBound  False []
tdTuple      = TyTag (-8)  [1, 1]      qualSet   True  [maxBound, maxBound]
  where qualSet = QualSet minBound (S.fromList [0, 1])

tdDual, tdSend, tdRecv, tdSelect, tdFollow :: TyTag
-- For session types:
tdDual       = TyTag (-11) [-1] minBound False []
tdSend       = TyTag (-12) [1]  minBound False [maxBound]
tdRecv       = TyTag (-13) [-1] minBound False [maxBound]
tdSelect     = TyTag (-14) [1]  minBound False [minBound]
tdFollow     = TyTag (-15) [1]  minBound False [minBound]

-- | Relay Haskell's IO exceptions
eiIOError      :: ExnId
eiIOError       = ExnId (-21) (Uid "IOError")      LC
-- | Contract blame errors
eiBlame        :: ExnId
eiBlame         = ExnId (-22) (Uid "Blame")        LC
-- | Failed pattern match errors
eiPatternMatch :: ExnId
eiPatternMatch  = ExnId (-23) (Uid "PatternMatch") LC

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

tyArrT         :: TypeT w -> TypeT w -> TypeT w
tyArrT a b      = TyCon (qlid "->") [a, b] tdArr

tyLolT         :: TypeT w -> TypeT w -> TypeT w
tyLolT a b      = TyCon (qlid "-o") [a, b] tdLol

tyTupleT       :: TypeT w -> TypeT w -> TypeT w
tyTupleT a b    = TyCon (qlid "*") [a, b] tdTuple

tyExnT         :: TypeT w
tyExnT          = TyCon (qlid "exn") [] tdExn

infixr 8 `tyArrT`, `tyLolT`
infixl 7 `tyTupleT`

-- | Find the qualifier of a type (which must be decorated with
--   tycon info)
qualifier     :: TypeT A -> Q
qualifier (TyCon _ ps td) = bigVee qs' where
  qs  = map qualifier ps
  qs' = q : map (qs !!) (S.toList ixs)
  QualSet q ixs = ttQual td
qualifier (TyVar (TV _ q))   = q
qualifier (TyQu _ _ t)       = qualifier t
qualifier (TyMu _ t)         = qualifier t
qualifier _                  = Qu

-- | Is a type transparent?
transparent :: forall w. Language w => TypeT w -> Bool
transparent t = case reifyLang :: LangRep w of
  C -> case t of
         TyCon _ _ td -> ttTrans td
         _            -> False
  A -> case t of
         TyCon _ _ td -> ttTrans td && (qualifier t <: Qu || td == tdTuple)
         _            -> False

-- | Constructors for function types
funtypes    :: [TyTag]
funtypes     = [tdArr, tdLol]

-- | Get all the A types embedded in a C type
cgetas :: Type i C -> [Type i A]
cgetas (TyCon _ ts _) = concatMap cgetas ts
cgetas (TyVar _)      = []
cgetas (TyQu _ _ t)   = cgetas t
cgetas (TyMu _ t)     = cgetas t
cgetas (TyA t)        = [t]
cgetas _              = [] -- can't happen

-- | Get all the C types embedded in a A type
agetcs :: Type i A -> [Type i C]
agetcs (TyCon _ ts _) = concatMap agetcs ts
agetcs (TyVar _)      = []
agetcs (TyQu _ _ t)   = agetcs t
agetcs (TyMu _ t)     = agetcs t
agetcs (TyC t)        = [t]
agetcs _              = [] -- can't happen

-- | Given a type tag and something traversable, find all type tags
--   with the same identity as the given type tag, and replace them.
--   (We use this to do type abstraction, since we can replace datatype
--   type tags with abstract type tags that have the datacons redacted.)
replaceTyTags :: Data a => TyTag -> a -> a
replaceTyTags tag' = everywhere (mkT each) where
  each :: TyTag -> TyTag
  each tag | ttId tag == ttId tag' = tag'
           | otherwise             = tag

-- | The C-to-A type translation
ctype2atype :: TypeT C -> TypeT A
ctype2atype t@(TyCon n ps td) | transparent t
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

-- | The A-to-C type translation
atype2ctype :: TypeT A -> TypeT C
atype2ctype t@(TyCon n ps td) | transparent t
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

-- | Is the expression conservatively side-effect free?
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

-- | Is the type promotable to a lower-qualifier type?
castableType :: TypeT w -> Bool
castableType (TyVar _)      = False
castableType (TyCon _ _ td) = td `elem` funtypes
castableType (TyQu _ _ t)   = castableType t
castableType (TyMu _ t)     = castableType t
castableType (TyC _)        = False
castableType (TyA _)        = False

-- | The name bound by a let declaration
letName :: Let i -> Lid
letName (LtA _ x _ _)   = x
letName (LtC _ x _ _)   = x
letName (LtInt _ x _ _) = x

-- | Turn a program into a sequence of declarations by replacing
-- the final expression with a declaration of variable 'it'.
prog2decls :: Prog i -> [Decl i]
prog2decls (Prog ds (Just e))
  = ds ++ [DcLet (getLoc e) (LtC True (Lid "it") Nothing e)]
prog2decls (Prog ds Nothing)
  = ds

-- Unfolding various sequences

-- | Get the list of formal parameters and body of a
--   lambda/typelambda expression
unfoldExAbs :: Expr i w -> ([Either (Patt, Type i w) TyVar], Expr i w)
unfoldExAbs  = unscanr each where
  each e = case view e of
    ExAbs x t e' -> Just (Left (x, t), e')
    ExTAbs tv e' -> Just (Right tv, e')
    _            -> Nothing

-- | Get the list of formal parameters and body of a qualified type
unfoldTyQu  :: Quant -> Type i w -> ([TyVar], Type i w)
unfoldTyQu u = unscanr each where
  each (TyQu u' x t) | u == u' = Just (x, t)
  each _                       = Nothing

-- | Get the list of actual parameters and body of a type application
unfoldExTApp :: Expr i w -> ([Type i w], Expr i w)
unfoldExTApp  = unscanl each where
  each e = case view e of
    ExTApp e' t  -> Just (t, e')
    _            -> Nothing

-- | Get the list of actual parameters and body of a value application
unfoldExApp :: Expr i w -> ([Expr i w], Expr i w)
unfoldExApp  = unscanl each where
  each e = case view e of
    ExApp e1 e2 -> Just (e2, e1)
    _           -> Nothing

-- | Get the list of argument types and result type of a function type
unfoldTyFun :: TypeT w -> ([TypeT w], TypeT w)
unfoldTyFun  = unscanr each where
  each (TyCon _ [ta, tr] td) | td `elem` funtypes = Just (ta, tr)
  each _                                         = Nothing

-- | Noisy type printer for debugging (includes type tags that aren't
--   normally pretty-printed)
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
