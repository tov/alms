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
      FlexibleInstances,
      MultiParamTypeClasses,
      ParallelListComp,
      TypeFamilies #-}
module Syntax (
  -- * Languages, variances, qualifiers
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
  isOperator, qlid, quid,

  -- * Types
  TyTag(..),
  Quant(..),
  Type(..),
  TypeT, TypeTEq(..),
  -- * Synthetic constructors
  tyAll, tyEx,
  -- ** Accessors and updaters
  tycon, tyargs, tyinfo,
  setTycon, setTyinfo,
  -- ** Freshness
  Ftv(..), freshTyVar, freshTyVars,
  -- ** Substitutions
  tysubst,
  -- ** Queries and conversions
  qualifier, funtypes, castableType,
  replaceTyTags, removeTyTags,
  (-==+),

  -- * Programs and declarations
  Prog(..), ProgT,
  Decl(..), DeclT,
  TyDec(..),
  AbsTy,
  ModExp(..), ModExpT,
  -- ** Synthetic consructors
  -- | These fill in the source location fields with a bogus location
  dcLet, dcTyp, dcAbs, dcMod, dcOpn, dcLoc, dcExn,
  -- ** Operations
  prog2decls,

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
  -- ** Optimizing expression constructors
  exLet', exLetVar', exAbs', exAbsVar', exTAbs',
  -- ** Expression accessors and updaters
  fv, exprType, (*:*), setExnId, getExnId, (*<*),
  syntacticValue,

  -- * Patterns and bindings
  Binding(..), BindingT, Patt(..),
  pv, ptv,

  -- * Partial orders
  PO(..), bigVee, bigVeeM, bigWedge, bigWedgeM,

  -- * Built-in types
  -- ** Type information
  tdUnit, tdInt, tdFloat, tdString, tdExn,
  tdArr, tdLol, tdTuple,
  -- ** Session types
  dualSessionType,
  tdDual, tdSend, tdRecv, tdSelect, tdFollow,
  -- ** Convenience type constructors
  tyNulOp, tyUnOp, tyBinOp,
  tyArr, tyLol, tyTuple,
  tyUnitT, tyArrT, tyLolT, tyTupleT, tyExnT,

  -- * Unfold syntax to lists
  unfoldExAbs, unfoldTyQu, unfoldExTApp, unfoldExApp, unfoldTyFun,
  unfoldTupleExpr, unfoldTuplePatt,

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
                      everywhere, mkT,
                      everything, mkQ)

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

-- | Info about a type constructor
data TyTag =
  TyTag {
    -- Identity
    ttId    :: Integer,
    -- The variance of each of its parameters
    ttArity :: [Variance],
    -- Determines qualifier as above
    ttQual  :: QualSet,
    -- upper qualifier bounds for parameters
    ttBound :: [Q]
  }
  deriving (Show, Typeable, Data)

-- | Types are parameterized by [@i@], the type of information
--   associated with each tycon
data Type i = TyCon QLid [Type i] i
            | TyVar TyVar
            | TyQu  Quant TyVar (Type i)
            | TyMu  TyVar (Type i)
  deriving Typeable

-- | Type quantifers
data Quant = Forall | Exists
  deriving (Typeable, Data, Eq)

tycon :: Type i -> QLid
tycon (TyCon tc _ _)  = tc
tycon _               = error "tycon: not a TyCon"
tyargs :: Type i -> [Type i]
tyargs (TyCon _ ts _) = ts
tyargs _              = error "tyargs: not a TyCon"
tyinfo :: Type i -> i
tyinfo (TyCon _ _ i)  = i
tyinfo _              = error "tyinfo: not a TyCon"

setTycon :: Type i -> QLid -> Type i
setTycon (TyCon _ ts i) tc = TyCon tc ts i
setTycon t _               = t
setTyinfo :: Type i -> i -> Type i
setTyinfo (TyCon tc ts _) i = TyCon tc ts i
setTyinfo t _               = t

infixl `setTycon`, `setTyinfo`

-- | Convenience constructors for qualified types
tyAll, tyEx :: TyVar -> Type i -> Type i
tyAll = TyQu Forall
tyEx  = TyQu Exists

-- | Remove tycon information from a type
removeTyTags :: Type i -> Type ()
removeTyTags  = untype where
  untype :: Type i -> Type ()
  untype (TyCon con args _) = TyCon con (map untype args) ()
  untype (TyVar tv)         = TyVar tv
  untype (TyQu quant tv t)  = TyQu quant tv (untype t)
  untype (TyMu tv t)        = TyMu tv (untype t)

-- | A program is a sequence of declarations, maybe followed by a C
-- expression
data Prog i = Prog [Decl i] (Maybe (Expr i))
  deriving (Typeable, Data)

-- | Declarations
data Decl i
  -- | Constant declaration
  = DcLet Loc Lid (Maybe (Type i)) (Expr i)
  -- | Type declaration
  | DcTyp Loc [TyDec]
  -- | Abstype block declaration
  | DcAbs Loc [AbsTy] [Decl i]
  -- | Module declaration
  | DcMod Loc Uid (ModExp i)
  -- | Module open
  | DcOpn Loc (ModExp i)
  -- | Local block
  | DcLoc Loc [Decl i] [Decl i]
  -- | Exception declaration
  | DcExn Loc Uid (Maybe (Type ()))
  deriving (Typeable, Data)

-- | Build a constant declaration with bogus source location
dcLet :: Lid -> Maybe (Type i) -> Expr i -> Decl i
dcLet  = DcLet bogus

-- | Build a type declaration with bogus source location
dcTyp :: [TyDec] -> Decl i
dcTyp  = DcTyp bogus

-- | Build a abstype declaration with bogus source location
dcAbs :: [AbsTy] -> [Decl i] -> Decl i
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
dcExn :: Uid -> Maybe (Type ()) -> Decl i
dcExn  = DcExn bogus

-- | Affine language type declarations
data TyDec
  -- | An abstract (empty) type
  = TdAbs {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    -- | The variance of each parameter
    tdaVariances :: [Variance],
    -- | Whether each parameter contributes to the qualifier
    tdaQual      :: [Either TyVar Q]
  }
  -- | A type synonym
  | TdSyn {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    tdaRHS       :: Type ()
  }
  -- | An algebraic datatype
  | TdDat {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    tdaAlts      :: [(Uid, Maybe (Type ()))]
  }
  deriving (Typeable, Data)

-- | An abstract type in language A needs to specify variances
-- and the qualifier
type AbsTy = ([Variance], [Either TyVar Q], TyDec)

-- | A module expression
data ModExp i
  -- | A module literal
  = MeStr [Decl i]
  -- | A module variable
  | MeName QUid
  deriving (Typeable, Data)

-- | Expressions are a two-level type, which simulates a sort
-- of inheritance without losing pattern matching.  Every expression
-- has several fields in addition to its particular abstract syntax.
data Expr i
  = Expr {
      -- | source location
      eloc_  :: Loc,
      -- | free variables
      fv_    :: FV,
      -- | possibly its type (used for translation)
      type_  :: Maybe TypeT,
      -- | if it's an exception constructor, its identity
      exnid_ :: Maybe ExnId,
      -- | the underlying sum type
      expr_  :: Expr' i
    }
  deriving (Typeable, Data)

-- | The underlying expression type, which we can pattern match without
-- dealing with the common fields above.
data Expr' i
  -- | variables and datacons
  = ExId Ident
  -- | string literals
  | ExStr String
  -- | integer literals
  | ExInt Integer
  -- | floating point literals
  | ExFloat Double
  -- | case expressions (including desugared @if@ and @let@)
  | ExCase (Expr i) [(Patt, Expr i)]
  -- | recursive let expressions
  | ExLetRec [Binding i] (Expr i)
  -- | nested declarations
  | ExLetDecl (Decl i) (Expr i)
  -- | pair construction
  | ExPair (Expr i) (Expr i)
  -- | lambda
  | ExAbs Patt (Type i) (Expr i)
  -- | application
  | ExApp (Expr i) (Expr i)
  -- | type abstraction
  | ExTAbs TyVar (Expr i)
  -- | type application
  | ExTApp (Expr i) (Type i)
  -- | existential construction
  | ExPack (Maybe (Type i)) (Type i) (Expr i)
  -- | dynamic promotion
  | ExCast (Expr i) (Maybe (Type i)) (Type i)
  deriving (Typeable, Data)

-- | Our free variables function returns not merely a set,
-- but a map from names to a count of maximum occurrences.
type FV        = M.Map QLid Integer

-- | Exceptions need identity beyond their names, since one
-- exception declaration can shadow another, and we need to catch
-- only the right ones a run time.
data ExnId     = ExnId {
                   eiIndex :: Integer,
                   eiName  :: Uid
                 }
  deriving (Eq, Show, Typeable, Data)

-- | Let-rec bindings require us to give types
data Binding i = Binding {
  bnvar  :: Lid,
  bntype :: Type i,
  bnexpr :: Expr i
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
-- | A type-checked module expression (has tycon info)
type ModExpT  = ModExp TyTag
-- | A type-checked let-rec binding (has tycon info)
type BindingT = Binding TyTag
-- | A type-checked program (has tycon info)
type ProgT    = Prog TyTag

-- | Accessor for the free variables field of expressions
fv :: Expr i -> FV
fv  = fv_

-- | Get the type of an expression, if known
exprType :: Expr i -> Maybe TypeT
exprType  = type_

-- | Update the type of an expression
(*:*) :: ExprT -> TypeT -> ExprT
e *:* t = e {
  type_ = Just t
}

-- | Get the exception id of an expression
getExnId :: Expr i -> Maybe ExnId
getExnId  = exnid_

-- | Update the exception id of an expression
setExnId :: Expr i -> Maybe ExnId -> Expr i
setExnId e mz = e { exnid_ = mz }

-- | Clone the type and exception id from the right expression
-- onto the left expression
(*<*) :: Expr i -> Expr i' -> Expr i
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

ptv :: Patt -> S.Set TyVar
ptv = everything S.union (mkQ S.empty S.singleton)

expr0 :: Expr i
expr0  = Expr {
  eloc_  = bogus,
  fv_    = M.empty,
  type_  = Nothing,
  exnid_ = Nothing,
  expr_  = undefined
}

mkexpr0   :: Expr' i -> Expr i
mkexpr0 e' = expr0 { expr_  = e' }

exStr :: String -> Expr i
exStr  = mkexpr0 . ExStr

exInt :: Integer -> Expr i
exInt  = mkexpr0 . ExInt

exFloat :: Double -> Expr i
exFloat  = mkexpr0 . ExFloat

exCase  :: Expr i -> [(Patt, Expr i)] -> Expr i
exCase e clauses = expr0 {
  eloc_  = getLoc (e, map snd clauses),
  fv_    = fv e |*|
           foldl (|+|) M.empty [ fv ex |--| pv x | (x, ex) <- clauses ],
  expr_  = ExCase e clauses
}

exLetRec :: [Binding i] -> Expr i -> Expr i
exLetRec bs e2 = expr0 {
  eloc_  = getLoc (bs, e2),
  fv_    = let es  = map bnexpr bs
               vs  = map (J [] . bnvar) bs
               pot = foldr (|*|) (fv e2) (map fv es)
           in foldl (|-|) pot vs,
  expr_  = ExLetRec bs e2
}

exLetDecl :: Decl i -> Expr i -> Expr i
exLetDecl d e2 = expr0 {
  eloc_  = getLoc (d, e2),
  fv_    = fv e2, -- conservative approximation
  expr_  = ExLetDecl d e2
}

exId :: Ident -> Expr i
exId x = expr0 {
  fv_    = case view x of
             Left y -> M.singleton y 1
             _      -> M.empty,
  expr_  = ExId x
}

exPair :: Expr i -> Expr i -> Expr i
exPair e1 e2 = expr0 {
  eloc_  = getLoc (e1, e2),
  fv_    = fv e1 |*| fv e2,
  expr_  = ExPair e1 e2
}

exAbs :: Patt -> Type i -> Expr i -> Expr i
exAbs x t e = expr0 {
  eloc_  = getLoc e,
  fv_    = fv e |--| pv x,
  expr_  = ExAbs x t e
}

exApp :: Expr i -> Expr i -> Expr i
exApp e1 e2 = expr0 {
  eloc_  = getLoc (e1, e2),
  fv_    = fv e1 |*| fv e2,
  expr_  = ExApp e1 e2
}

exTAbs :: TyVar -> Expr i -> Expr i
exTAbs tv e = expr0 {
  eloc_  = getLoc e,
  fv_    = fv e,
  expr_  = ExTAbs tv e
}

exTApp :: Expr i -> Type i -> Expr i
exTApp e1 t2 = expr0 {
  eloc_  = getLoc e1,
  fv_    = fv e1,
  expr_  = ExTApp e1 t2
}

exPack :: Maybe (Type i) -> Type i -> Expr i -> Expr i
exPack t1 t2 e = expr0 {
  eloc_  = getLoc e,
  fv_    = fv e,
  expr_  = ExPack t1 t2 e
}

exCast :: Expr i -> Maybe (Type i) -> Type i -> Expr i
exCast e t1 t2 = expr0 {
  eloc_  = getLoc e,
  fv_    = fv e,
  expr_  = ExCast e t1 t2
}

exVar :: QLid -> Expr i
exVar  = exId . fmap Var

exCon :: QUid -> Expr i
exCon  = exId . fmap Con

exBVar :: Lid -> Expr i
exBVar  = exId . J [] . Var

exBCon :: Uid -> Expr i
exBCon  = exId . J [] . Con

exLet :: Patt -> Expr i -> Expr i -> Expr i
exLet x e1 e2 = exCase e1 [(x, e2)]

exSeq :: Expr i -> Expr i -> Expr i
exSeq e1 e2 = exCase e1 [(PaWild, e2)]

-- | Constructs a let expression, but with a special case:
--
--   @let x      = e in x        ==   e@
--   @let (x, y) = e in (x, y)   ==   e@
--
-- This is always safe to do.
exLet' :: Patt -> Expr i -> Expr i -> Expr i
exLet' x e1 e2 = if (x -==+ e2) then e1 else exLet x e1 e2

-- | Constructs a let expression whose pattern is a variable.
exLetVar' :: Lid -> Expr i -> Expr i -> Expr i
exLetVar'  = exLet' . PaVar

-- | Constructs a lambda expression, but with a special case:
--
--    @exAbs' x t (exApp (exVar f) (exVar x))  ==  exVar f@
--
-- This eta-contraction is always safe, because f has no effect
exAbs' :: Patt -> Type i -> Expr i -> Expr i
exAbs' x t e = case view e of
  ExApp e1 e2 -> case (x, view e1, view e2) of
    (PaVar y, ExId (J p (Var f)), ExId (J [] (Var y'))) |
      y == y' && J [] y /= J p f
              -> exVar (J p f)
    _         -> exAbs x t e
  _           -> exAbs x t e

-- | Construct an abstraction whose pattern is just a variable.
exAbsVar' :: Lid -> Type i -> Expr i -> Expr i
exAbsVar'  = exAbs' . PaVar

-- | Construct a type-lambda expression, but with a special case:
--
--   @exTAbs' tv (exTApp (exVar f) tv)  ==  exVar f@
--
-- This should always be safe, because f has no effect
exTAbs' :: TyVar -> Expr i -> Expr i
exTAbs' tv e = case view e of
  ExTApp e1 t2 -> case (view e1, t2) of
    (ExId (J p (Var f)), TyVar tv') |
      tv == tv'  -> exVar (J p f)
    _            -> exTAbs tv e
  _            -> exTAbs tv e

-- | Does a pattern exactly match an expression?  That is, is
--   @let p = e1 in e@ equivalent to @e1@?  Note that we cannot
--   safely handle data constructors, because they may fail to match.
(-==+) :: Patt -> Expr i -> Bool
p -==+ e = case (p, view e) of
  (PaVar l,                   ExId (J [] (Var l')))
    -> l == l'
  (PaCon (Uid "()") Nothing Nothing,   ExId (J [] (Con (Uid "()"))))
    -> True
  (PaPair p1 p2,              ExPair e1 e2)
    -> p1 -==+ e1 && p2 -==+ e2
  _ -> False
infix 4 -==+

-- | Is the lowercase identifier an infix operator?
isOperator :: Lid -> Bool
isOperator lid = case show lid of
    '(':_ -> True
    _     -> False

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

instance Data i => Data (Type i) where
   gfoldl k z (TyCon a b c) = z TyCon `k` a `k` b `k` c
   gfoldl k z (TyVar a)     = z TyVar `k` a
   gfoldl k z (TyQu u a b)  = z TyQu  `k` u `k` a `k` b
   gfoldl k z (TyMu a b)    = z TyMu  `k` a `k` b

   gunfold k z c = case constrIndex c of
                       1 -> k $ k $ k $ z TyCon
                       2 -> k $ z TyVar
                       3 -> k $ k $ k $ z TyQu
                       4 -> k $ k $ z TyMu
                       _ -> error "gunfold(Type): bad constrIndex"

   toConstr (TyCon _ _ _) = con_TyCon
   toConstr (TyVar _)     = con_TyVar
   toConstr (TyQu _ _ _)  = con_TyQu
   toConstr (TyMu _ _)    = con_TyMu

   dataTypeOf _ = ty_Type

con_TyCon, con_TyVar, con_TyQu, con_TyMu
        :: Constr
ty_Type :: DataType
con_TyCon = mkConstr ty_Type "TyCon" [] Prefix
con_TyVar = mkConstr ty_Type "TyVar" [] Prefix
con_TyQu  = mkConstr ty_Type "TyQu"  [] Prefix
con_TyMu  = mkConstr ty_Type "TyMu"  [] Prefix
ty_Type = mkDataType "Syntax.Type"
            [ con_TyCon, con_TyVar, con_TyQu, con_TyMu ]

instance (Ord p, (:>:) k k') =>
         (:>:) (Path p k) k'  where liftKey = J [] . liftKey
instance (:>:) BIdent Lid     where liftKey = Var
instance (:>:) BIdent Uid     where liftKey = Con

instance Eq TyTag where
  td == td' = ttId td == ttId td'

instance Viewable (Path Uid BIdent) where
  type View Ident = Either QLid QUid
  view (J p (Var n)) = Left (J p n)
  view (J p (Con n)) = Right (J p n)

instance Viewable (Expr i) where
  type View (Expr i) = Expr' i
  view = expr_

instance Locatable (Expr i) where
  getLoc       = eloc_

instance Relocatable (Expr i) where
  setLoc e loc = e { eloc_ = loc }

instance Locatable (Decl i) where
  getLoc (DcLet loc _ _ _) = loc
  getLoc (DcTyp loc _)     = loc
  getLoc (DcAbs loc _ _)   = loc
  getLoc (DcMod loc _ _)   = loc
  getLoc (DcOpn loc _)     = loc
  getLoc (DcLoc loc _ _)   = loc
  getLoc (DcExn loc _ _)   = loc

instance Relocatable (Decl i) where
  setLoc (DcLet _ n t e) loc = DcLet loc n t e
  setLoc (DcTyp _ td)    loc = DcTyp loc td
  setLoc (DcAbs _ at ds) loc = DcAbs loc at ds
  setLoc (DcMod _ m b)   loc = DcMod loc m b
  setLoc (DcOpn _ m)     loc = DcOpn loc m
  setLoc (DcLoc _ d d')  loc = DcLoc loc d d'
  setLoc (DcExn _ u e)   loc = DcExn loc u e

instance Locatable (Binding i) where
  getLoc = getLoc . bnexpr

instance Eq QualSet where
  QualSet q ixs == QualSet q' ixs'
    | q == maxBound && q' == maxBound = True
    | otherwise                       = q == q' && ixs == ixs'

data TypeTEq = TypeTEq { unTypeTEq :: TypeT }

-- On TypeTEq, we define simple alpha equality, which we then use
-- to keep track of where we've been when we define type equality
-- that understands mu.
instance Eq TypeTEq where
  te1 == te2 = unTypeTEq te1 === unTypeTEq te2
    where
      (===) :: TypeT -> TypeT -> Bool
      TyCon _ ps td === TyCon _ ps' td'
                                 = td == td' && all2 (===) ps ps'
      TyVar x       === TyVar x' = x == x'
      TyQu u x t    === TyQu u' x' t'
        | u == u' && tvqual x == tvqual x' =
          tysubst x a t === tysubst x' a t'
            where a = TyVar (freshTyVar x (ftv [t, t']))
      TyMu x t      === TyMu x' t'
        | tvqual x == tvqual x' =
          tysubst x a t === tysubst x' a t'
            where a = TyVar (freshTyVar x (ftv [t, t']))
      _             === _        = False

instance Eq (Type TyTag) where
  (==) t1i t2i = evalState (t1i `chk` t2i) [] where
    chk, cmp :: TypeT -> TypeT -> State [(TypeTEq, TypeTEq)] Bool
    t1 `chk` t2 = do
      seen <- get
      let te1 = TypeTEq t1; te2 = TypeTEq t2
      if (te1, te2) `elem` seen
        then return True
        else do
          put ((te1, te2) : (te2, te1) : seen)
          cmp t1 t2

    TyCon _ [p] td `cmp` t
      | td == tdDual                     = dualSessionType p `chk` t
    t              `cmp` TyCon _ [p] td
      | td == tdDual                     = t `chk` dualSessionType p
    TyMu a t       `cmp` t'              = tysubst a (TyMu a t) t `chk` t'
    t'             `cmp` TyMu a t        = t' `chk` tysubst a (TyMu a t) t
    TyCon _ ps td  `cmp` TyCon _ ps' td'
      | td == td'   = allM2 chk ps ps'
    TyVar x        `cmp` TyVar x'        = return (x == x')
    TyQu u x t     `cmp` TyQu u' x' t' 
      | u == u' && tvqual x == tvqual x' = 
        tysubst x a t `chk` tysubst x' a t'
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
    c  :_ | isDigit c -> (s++)
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
--  * '\/', '/\'    (only if it's a lattice)
--
--  * '\/?', '/\?'  (partial join and meet)
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
instance  PO (Type TyTag) where
  ifMJ bi t1i t2i = clean `liftM` chk [] bi t1i t2i where
    clean :: TypeT -> TypeT
    clean (TyCon c ps td)  = TyCon c (map clean ps) td
    clean (TyVar a)        = TyVar a
    clean (TyQu u a t)     = TyQu u a (clean t)
    clean (TyMu a t)
      | a `S.member` ftv t = TyMu a (clean t)
      | otherwise          = clean t

    chk, cmp :: Monad m =>
                [((Bool, TypeTEq, TypeTEq), TyVar)] ->
                Bool -> TypeT -> TypeT ->
                m TypeT
    chk seen b t1 t2 = do
      let te1 = TypeTEq t1; te2 = TypeTEq t2
      case lookup (b, te1, te2) seen of
        Just tv -> return (TyVar tv)
        Nothing -> TyMu tv `liftM` cmp seen' b t1 t2 where
          used  = S.fromList (map snd seen)
          tv    = freshTyVar (TV (Lid "r") (qualifier t1 \/ qualifier t2))
                             (ftv [t1, t2] `S.union` used)
          seen' = (((b, te1, te2), tv) : ((b, te2, te1), tv) : seen)

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
          t1  = tysubst a (TyVar a1) t
          t'1 = tysubst a' (TyVar a1) t'
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

---
--- Syntax Utils
---

-- | Class for getting free type variables (from types, expressions,
-- lists thereof, pairs thereof, etc.)
class Ftv a where
  ftv :: a -> S.Set TyVar

instance Ftv (Type i) where
  ftv (TyCon _ ts _) = S.unions (map ftv ts)
  ftv (TyVar tv)     = S.singleton tv
  ftv (TyQu _ tv t)  = S.delete tv (ftv t)
  ftv (TyMu tv t)    = S.delete tv (ftv t)

instance Ftv a => Ftv [a] where
  ftv = S.unions . map ftv

instance Ftv TyVar where
  ftv = S.singleton

instance (Ftv a, Ftv b) => Ftv (a, b) where
  ftv (a, b) = ftv a `S.union` ftv b

class FtvVs a where
  ftvVs :: a -> M.Map TyVar Variance

instance FtvVs (Type TyTag) where
  ftvVs (TyCon _ ts td)= M.unionsWith (+)
                         [ M.map (* var) m
                         | var <- ttArity td
                         | m   <- map ftvVs ts ]
  ftvVs (TyVar tv)     = M.singleton tv 1
  ftvVs (TyQu _ tv t)  = M.delete tv (ftvVs t)
  ftvVs (TyMu tv t)    = M.delete tv (ftvVs t)

instance FtvVs a => FtvVs [a] where
  ftvVs = M.unionsWith (+) . map ftvVs

instance FtvVs TyVar where
  ftvVs tv = M.singleton tv 1

instance (FtvVs a, FtvVs b) => FtvVs (a, b) where
  ftvVs (a, b) = M.unionWith (+) (ftvVs a) (ftvVs b)

freshTyVars :: [TyVar] -> S.Set TyVar -> [TyVar]
freshTyVars tvs0 s0 = loop tvs0 (s0 `S.union` S.fromList tvs0) where
  loop (tv:tvs) s' = let tv' = freshTyVar tv s'
                      in tv' : loop tvs (S.insert tv' s')
  loop _        _ = []

freshTyVar :: TyVar -> S.Set TyVar -> TyVar
freshTyVar tv s = if tv `S.member` s
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
      in if tv' `S.member` s
           then loop (n + 1)
           else tv'

-- | Type substitution (NB: the languages need not match, since
-- types embed in one another)
tysubst :: TyVar -> Type i -> Type i -> Type i
tysubst a t = ts where
  ts (TyVar a')
                = if a' == a
                    then t
                    else TyVar a'
  ts (TyQu u a' t')
                = if a' == a
                    then TyQu u a' t'
                    else
                     let a'' = freshTyVar a' (ftv (a, [t, t']))
                      in TyQu u a'' (ts (tysubst a' (TyVar a'') t'))
  ts (TyMu a' t')
                = if a' == a
                    then TyMu a' t'
                    else
                     let a'' = freshTyVar a' (ftv (a, [t, t']))
                      in TyMu a'' (ts (tysubst a' (TyVar a'') t'))
  ts (TyCon c tys td)
                = TyCon c (map ts tys) td

-- |
-- Helper for finding the dual of a session type (since we can't
-- express this directly in the type system at this point)
dualSessionType :: TypeT -> TypeT
dualSessionType  = d where
  d (TyCon (J [] (Lid ";"))
       [TyCon (J [] (Lid "send")) [ta] _, tr] tdSemi)
    = TyCon (qlid ";") [TyCon (qlid "recv") [ta] tdRecv, d tr] tdSemi
  d (TyCon (J [] (Lid ";"))
       [TyCon (J [] (Lid "recv")) [ta] _, tr] tdSemi)
    = TyCon (qlid ";") [TyCon (qlid "send") [ta] tdSend, d tr] tdSemi
  d (TyCon (J [] (Lid "select"))
       [TyCon (J [] (Lid "+")) [t1, t2] tdSum] _)
    = TyCon (qlid "follow") [TyCon (qlid "+") [d t1, d t2] tdSum] tdFollow
  d (TyCon (J [] (Lid "follow"))
       [TyCon (J [] (Lid "+")) [t1, t2] tdSum] _)
    = TyCon (qlid "select") [TyCon (qlid "+") [d t1, d t2] tdSum] tdSelect
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

tdUnit       = TyTag (-1)  []          minBound  []
tdInt        = TyTag (-2)  []          minBound  []
tdFloat      = TyTag (-3)  []          minBound  []
tdString     = TyTag (-4)  []          minBound  []
tdArr        = TyTag (-5)  [-1, 1]     minBound  [maxBound, maxBound]
tdLol        = TyTag (-6)  [-1, 1]     maxBound  [maxBound, maxBound]
tdExn        = TyTag (-7)  []          maxBound  []
tdTuple      = TyTag (-8)  [1, 1]      qualSet   [maxBound, maxBound]
  where qualSet = QualSet minBound (S.fromList [0, 1])

tdDual, tdSend, tdRecv, tdSelect, tdFollow :: TyTag
-- For session types:
tdDual       = TyTag (-11) [-1] minBound []
tdSend       = TyTag (-12) [1]  minBound [maxBound]
tdRecv       = TyTag (-13) [-1] minBound [maxBound]
tdSelect     = TyTag (-14) [1]  minBound [minBound]
tdFollow     = TyTag (-15) [1]  minBound [minBound]

-- | Relay Haskell's IO exceptions
eiIOError      :: ExnId
eiIOError       = ExnId (-21) (Uid "IOError")
-- | Contract blame errors
eiBlame        :: ExnId
eiBlame         = ExnId (-22) (Uid "Blame")
-- | Failed pattern match errors
eiPatternMatch :: ExnId
eiPatternMatch  = ExnId (-23) (Uid "PatternMatch")

tyNulOp       :: String -> Type ()
tyNulOp s      = TyCon (qlid s) [] ()

tyUnOp        :: String -> Type () -> Type ()
tyUnOp s a     = TyCon (qlid s) [a] ()

tyBinOp       :: String -> Type () -> Type () -> Type ()
tyBinOp s a b  = TyCon (qlid s) [a, b] ()

tyArr         :: Type () -> Type () -> Type ()
tyArr          = tyBinOp "->"

tyLol         :: Type () -> Type () -> Type ()
tyLol          = tyBinOp "-o"

tyTuple       :: Type () -> Type () -> Type ()
tyTuple        = tyBinOp "*"

tyUnitT        :: TypeT
tyUnitT         = TyCon (qlid "unit") [] tdUnit

tyArrT         :: TypeT -> TypeT -> TypeT
tyArrT a b      = TyCon (qlid "->") [a, b] tdArr

tyLolT         :: TypeT -> TypeT -> TypeT
tyLolT a b      = TyCon (qlid "-o") [a, b] tdLol

tyTupleT       :: TypeT -> TypeT -> TypeT
tyTupleT a b    = TyCon (qlid "*") [a, b] tdTuple

tyExnT         :: TypeT
tyExnT          = TyCon (qlid "exn") [] tdExn

infixr 8 `tyArrT`, `tyLolT`
infixl 7 `tyTupleT`

-- | Find the qualifier of a type (which must be decorated with
--   tycon info)
qualifier     :: TypeT -> Q
qualifier (TyCon _ ps td) = bigVee qs' where
  qs  = map qualifier ps
  qs' = q : map (qs !!) (S.toList ixs)
  QualSet q ixs = ttQual td
qualifier (TyVar (TV _ q))   = q
qualifier (TyQu _ _ t)       = qualifier t
qualifier (TyMu _ t)         = qualifier t

-- | Constructors for function types
funtypes    :: [TyTag]
funtypes     = [tdArr, tdLol]

-- | Given a type tag and something traversable, find all type tags
--   with the same identity as the given type tag, and replace them.
--   (We use this to do type abstraction, since we can replace datatype
--   type tags with abstract type tags that have the datacons redacted.)
replaceTyTags :: Data a => TyTag -> a -> a
replaceTyTags tag' = everywhere (mkT each) where
  each :: TyTag -> TyTag
  each tag | ttId tag == ttId tag' = tag'
           | otherwise             = tag

-- | Is the expression conservatively side-effect free?
syntacticValue :: Expr i -> Bool
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

syntacticConstructor :: Expr i -> Bool
syntacticConstructor e = case view e of
  ExId (J [] (Con _)) -> True
  ExTApp e1 _         -> syntacticConstructor e1
  ExApp e1 e2         -> syntacticConstructor e1 && syntacticValue e2
  _                   -> False

-- | Is the type promotable to a lower-qualifier type?
castableType :: TypeT -> Bool
castableType (TyVar _)      = False
castableType (TyCon _ _ td) = td `elem` funtypes
castableType (TyQu _ _ t)   = castableType t
castableType (TyMu _ t)     = castableType t

-- | Turn a program into a sequence of declarations by replacing
-- the final expression with a declaration of variable 'it'.
prog2decls :: Prog i -> [Decl i]
prog2decls (Prog ds (Just e))
  = ds ++ [DcLet (getLoc e) (Lid "it") Nothing e]
prog2decls (Prog ds Nothing)
  = ds

-- Unfolding various sequences

-- | Get the list of formal parameters and body of a
--   lambda/typelambda expression
unfoldExAbs :: Expr i -> ([Either (Patt, Type i) TyVar], Expr i)
unfoldExAbs  = unscanr each where
  each e = case view e of
    ExAbs x t e' -> Just (Left (x, t), e')
    ExTAbs tv e' -> Just (Right tv, e')
    _            -> Nothing

-- | Get the list of formal parameters and body of a qualified type
unfoldTyQu  :: Quant -> Type i -> ([TyVar], Type i)
unfoldTyQu u = unscanr each where
  each (TyQu u' x t) | u == u' = Just (x, t)
  each _                       = Nothing

-- | Get the list of actual parameters and body of a type application
unfoldExTApp :: Expr i -> ([Type i], Expr i)
unfoldExTApp  = unscanl each where
  each e = case view e of
    ExTApp e' t  -> Just (t, e')
    _            -> Nothing

-- | Get the list of actual parameters and body of a value application
unfoldExApp :: Expr i -> ([Expr i], Expr i)
unfoldExApp  = unscanl each where
  each e = case view e of
    ExApp e1 e2 -> Just (e2, e1)
    _           -> Nothing

-- | Get the list of argument types and result type of a function type
unfoldTyFun :: TypeT -> ([TypeT], TypeT)
unfoldTyFun  = unscanr each where
  each (TyCon _ [ta, tr] td) | td `elem` funtypes = Just (ta, tr)
  each _                                         = Nothing

unfoldTupleExpr :: Expr i -> ([Expr i], Expr i)
unfoldTupleExpr  = unscanl each where
  each e = case view e of
    ExPair e1 e2 -> Just (e2, e1)
    _            -> Nothing

unfoldTuplePatt :: Patt -> ([Patt], Patt)
unfoldTuplePatt  = unscanl each where
  each p = case p of
    PaPair p1 p2 -> Just (p2, p1)
    _            -> Nothing

-- | Noisy type printer for debugging (includes type tags that aren't
--   normally pretty-printed)
dumpType :: Int -> TypeT -> IO ()
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
