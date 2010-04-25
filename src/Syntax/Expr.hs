{-# LANGUAGE
      DeriveDataTypeable,
      TypeFamilies #-}
module Syntax.Expr (
  -- * Expressions
  Expr(..), ExprT, Expr'(..),
  -- ** Letrec bindings
  Binding(..), BindingT,

  -- * Two-level expression constructors
  -- | These fill in the source location field based on the
  -- subexpressions and perform the free variable analysis
  exId, exLit, exCase, exLetRec, exLetDecl, exPair,
  exAbs, exApp, exTAbs, exTApp, exPack, exCast, exAnti,
  -- ** Synthetic expression constructors
  exVar, exCon, exBVar, exBCon,
  exStr, exInt, exFloat,
  exLet, exSeq,
  -- ** Optimizing expression constructors
  exLet', exLetVar', exAbs', exAbsVar', exTAbs',

  -- * Expression accessors and updaters
  fv, setExn, isExn, (*<*),
  syntacticValue
) where

import Loc as Loc
import Syntax.Anti
import Syntax.Ident
import Syntax.Type
import Syntax.Lit
import Syntax.Patt
import {-# SOURCE #-} Syntax.Decl
import Viewable

import Data.Generics (Typeable(..), Data(..))
import qualified Data.Map as M
import qualified Data.Set as S

-- | Our free variables function returns not merely a set,
-- but a map from names to a count of maximum occurrences.
type FV        = M.Map QLid Integer

-- | Expressions are a two-level type, which simulates a sort
-- of inheritance without losing pattern matching.  Every expression
-- has several fields in addition to its particular abstract syntax.
data Expr i
  = Expr {
      -- | source location
      eloc_  :: Loc,
      -- | free variables
      fv_    :: FV,
      -- | is it an exception constructor?
      isexn_ :: Bool,
      -- | the underlying sum type
      expr_  :: Expr' i
    }
  deriving (Typeable, Data)

-- | The underlying expression type, which we can pattern match without
-- dealing with the common fields above.
data Expr' i
  -- | variables and datacons
  = ExId Ident
  -- | literals
  | ExLit Lit
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
  -- | antiquotes
  | ExAnti Anti
  deriving (Typeable, Data)

-- | Let-rec bindings require us to give types
data Binding i = Binding {
  bnvar  :: Lid,
  bntype :: Type i,
  bnexpr :: Expr i
}
  deriving (Typeable, Data)

-- | A type-checked expression (has tycon info)
type ExprT    = Expr TyTag
-- | A type-checked let-rec binding (has tycon info)
type BindingT = Binding TyTag

-- | Accessor for the free variables field of expressions
fv :: Expr i -> FV
fv  = fv_

-- | Is the given expression an exception constructor?
isExn :: Expr i -> Bool
isExn  = isexn_

-- | Make the expression an exception constructor
setExn :: Expr i -> Bool -> Expr i
setExn e b = e { isexn_ = b }

-- | Clone the type and exceptionness from the right expression
-- onto the left expression
(*<*) :: Expr i -> Expr i' -> Expr i
e *<* e' = e { isexn_ = isexn_ e' }

expr0 :: Expr i
expr0  = Expr {
  eloc_  = bogus,
  fv_    = M.empty,
  isexn_ = False,
  expr_  = undefined
}

mkexpr0   :: Expr' i -> Expr i
mkexpr0 e' = expr0 { expr_  = e' }

exLit :: Lit -> Expr i
exLit  = mkexpr0 . ExLit

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

exAnti :: Anti -> Expr i
exAnti a = expr0 {
  fv_    = antierror "fv" a,
  expr_  = ExAnti a
}

exVar :: QLid -> Expr i
exVar  = exId . fmap Var

exCon :: QUid -> Expr i
exCon  = exId . fmap Con

exBVar :: Lid -> Expr i
exBVar  = exId . J [] . Var

exBCon :: Uid -> Expr i
exBCon  = exId . J [] . Con

exStr :: String -> Expr i
exStr  = exLit . LtStr

exInt :: Integer -> Expr i
exInt  = exLit . LtInt

exFloat :: Double -> Expr i
exFloat  = exLit . LtFloat

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
  (PaVar l,      ExId (J [] (Var l')))
    -> l == l'
  (PaCon (J [] (Uid "(")) Nothing False,
   ExId (J [] (Con (Uid "()"))))
    -> True
  (PaPair p1 p2, ExPair e1 e2)
    -> p1 -==+ e1 && p2 -==+ e2
  _ -> False
infix 4 -==+

-- | Used by the free variables analysis
(|*|), (|+|) :: FV -> FV -> FV
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: FV -> QLid -> FV
(|-|)  = flip M.delete

(|--|) :: FV -> S.Set Lid -> FV
(|--|)  = S.fold (M.delete . J [])

instance Viewable (Expr i) where
  type View (Expr i) = Expr' i
  view = expr_

instance Locatable (Expr i) where
  getLoc       = eloc_

instance Relocatable (Expr i) where
  setLoc e loc = e { eloc_ = loc }

instance Locatable (Binding i) where
  getLoc = getLoc . bnexpr

-- | Is the expression conservatively side-effect free?
syntacticValue :: Expr i -> Bool
syntacticValue e = case view e of
  ExId _       -> True
  ExLit _      -> True
  ExPair e1 e2 -> syntacticValue e1 && syntacticValue e2
  ExAbs _ _ _  -> True
  ExApp e1 e2  -> syntacticConstructor e1 && syntacticValue e2
  ExTAbs _ _   -> True
  ExTApp e1 _  -> syntacticValue e1
  ExAnti a     -> antierror "syntacticValue" a
  _            -> False

syntacticConstructor :: Expr i -> Bool
syntacticConstructor e = case view e of
  ExId (J [] (Con _)) -> True
  ExTApp e1 _         -> syntacticConstructor e1
  ExApp e1 e2         -> syntacticConstructor e1 && syntacticValue e2
  ExAnti a            -> antierror "syntacticConstructor" a
  _                   -> False

