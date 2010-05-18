{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      TemplateHaskell,
      TypeFamilies,
      TypeSynonymInstances #-}
module Syntax.Expr (
  -- * Expressions
  Expr'(..), Expr, ExprNote(..), newExpr,
  -- ** Letrec and case
  Binding'(..), Binding, newBinding,
  CaseAlt'(..), CaseAlt, newCaseAlt,

  -- * Two-level expression constructors
  -- | These fill in the source location field based on the
  -- subexpressions and perform the free variable analysis
  exId, exLit, exCase, exLetRec, exLetDecl, exPair,
  exAbs, exApp, exTAbs, exTApp, exPack, exCast, exAnti,
  caClause, caAnti,
  bnBind, bnAnti,
  -- ** Synthetic expression constructors
  exVar, exCon, exBVar, exBCon,
  exStr, exInt, exFloat,
  exLet, exSeq,
  -- ** Optimizing expression constructors
  exLet', exLetVar', exAbs', exAbsVar', exTAbs',

  -- * Expression accessors and updaters
  syntacticValue
) where

import Syntax.Notable
import Syntax.Anti
import Syntax.Ident
import Syntax.Type
import Syntax.Lit
import Syntax.Patt
import {-# SOURCE #-} Syntax.Decl
import Viewable

import Meta.DeriveNotable

import Data.Generics (Typeable(..), Data(..))
import qualified Data.Map as M

type Expr i    = N (ExprNote i) (Expr' i)
type Binding i = N (ExprNote i) (Binding' i)
type CaseAlt i = N (ExprNote i) (CaseAlt' i)

-- | The underlying expression type, which we can pattern match without
-- dealing with the common fields above.
data Expr' i
  -- | variables and datacons
  = ExId (Ident i)
  -- | literals
  | ExLit Lit
  -- | case expressions (including desugared @if@ and @let@)
  | ExCase (Expr i) [CaseAlt i]
  -- | recursive let expressions
  | ExLetRec [Binding i] (Expr i)
  -- | nested declarations
  | ExLetDecl (Decl i) (Expr i)
  -- | pair construction
  | ExPair (Expr i) (Expr i)
  -- | lambda
  | ExAbs (Patt i) (Type i) (Expr i)
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
data Binding' i
  = BnBind {
      bnvar  :: Lid i,
      bntype :: Type i,
      bnexpr :: Expr i
    }
  | BnAnti Anti
  deriving (Typeable, Data)

data CaseAlt' i
  = CaClause {
      capatt :: Patt i,
      caexpr :: Expr i
    }
  | CaAnti Anti
  deriving (Typeable, Data)

-- | The annotation on every expression
data ExprNote i
  = ExprNote {
      -- | source location
      eloc_  :: !Loc,
      -- | free variables
      efv_   :: FvMap i
    }
  deriving (Typeable, Data)

instance Locatable (ExprNote i) where
  getLoc = eloc_

instance Relocatable (ExprNote i) where
  setLoc note loc = note { eloc_ = loc }

-- | Types with free variable analyses
instance Id i => Fv (N (ExprNote i) a) i where fv = efv_ . noteOf

instance Notable (ExprNote i) where
  newNote = ExprNote {
    eloc_  = bogus,
    efv_   = M.empty
  }

newExpr :: Id i => Expr' i -> Expr i
newExpr e0 = flip N e0 $ case e0 of
  ExId i  ->
    newNote {
      efv_ = case view i of
               Left y -> M.singleton y 1
               _      -> M.empty
      }
  ExLit _ -> newNote
  ExCase e1 cas ->
    newNote {
      efv_  = fv e1 |*| fv (ADDITIVE cas),
      eloc_ = getLoc (e1, cas)
    }
  ExLetRec bns e2 ->
    newNote {
      efv_  = let vs  = map (J [] . bnvar . dataOf) bns
                  pot = fv e2 |+| fv bns
              in foldl (|-|) pot vs,
      eloc_ = getLoc (bns, e2)
    }
  ExLetDecl d1 e2 ->
    newNote {
      efv_  = fv d1 |*| (fv e2 |--| qdv d1),
      eloc_ = getLoc (d1, e2)
    }
  ExPair e1 e2 ->
    newNote {
      efv_  = fv e1 |*| fv e2,
      eloc_ = getLoc (e1, e2)
    }
  ExAbs p1 _ e3 ->
    newNote {
      efv_  = fv e3 |--| qdv p1,
      eloc_ = getLoc (p1, e3)
    }
  ExApp e1 e2 ->
    newNote {
      efv_  = fv e1 |*| fv e2,
      eloc_ = getLoc (e1, e2)
    }
  ExTAbs _ e2 ->
    newNote {
      efv_  = fv e2,
      eloc_ = getLoc e2
    }
  ExTApp e1 t2 ->
    newNote {
      efv_  = fv e1,
      eloc_ = getLoc (e1, t2)
    }
  ExPack mt1 t2 e3 ->
    newNote {
      efv_  = fv e3,
      eloc_ = getLoc (mt1, t2, e3)
    }
  ExCast e1 mt2 t3 ->
    newNote {
      efv_  = fv e1,
      eloc_ = getLoc (e1, mt2, t3)
    }
  ExAnti a ->
    newNote {
      efv_  = antierror "fv" a
    }

newBinding :: Id i => Binding' i -> Binding i
newBinding b0 = flip N b0 $ case b0 of
  BnBind x t e ->
    newNote {
      efv_  = fv e |-| J [] x,
      eloc_ = getLoc (t, e)
    }
  BnAnti a ->
    newNote {
      efv_  = antierror "fv" a
    }

newCaseAlt :: Id i => CaseAlt' i -> CaseAlt i
newCaseAlt ca0 = flip N ca0 $ case ca0 of
  CaClause x e ->
    newNote {
      efv_  = fv e |--| qdv x,
      eloc_ = getLoc (x, e)
    }
  CaAnti a ->
    newNote {
      efv_  = antierror "fv" a
    }

deriveNotable 'newExpr    (''Id, [0]) ''Expr
deriveNotable 'newCaseAlt (''Id, [0]) ''CaseAlt
deriveNotable 'newBinding (''Id, [0]) ''Binding

exVar :: Id i => QLid i -> Expr i
exVar  = exId . fmap Var

exCon :: Id i => QUid i -> Expr i
exCon  = exId . fmap Con

exBVar :: Id i => Lid i -> Expr i
exBVar  = exId . J [] . Var

exBCon :: Id i => Uid i -> Expr i
exBCon  = exId . J [] . Con

exStr :: Id i => String -> Expr i
exStr  = exLit . LtStr

exInt :: Id i => Integer -> Expr i
exInt  = exLit . LtInt

exFloat :: Id i => Double -> Expr i
exFloat  = exLit . LtFloat

exLet :: Id i => Patt i -> Expr i -> Expr i -> Expr i
exLet x e1 e2 = exCase e1 [caClause x e2]

exSeq :: Id i => Expr i -> Expr i -> Expr i
exSeq e1 e2 = exCase e1 [caClause paWild e2]

-- | Constructs a let expression, but with a special case:
--
--   @let x      = e in x        ==   e@
--   @let (x, y) = e in (x, y)   ==   e@
--
-- This is always safe to do.
exLet' :: Id i => Patt i -> Expr i -> Expr i -> Expr i
exLet' x e1 e2 = if (x -==+ e2) then e1 else exLet x e1 e2

-- | Constructs a let expression whose pattern is a variable.
exLetVar' :: Id i => Lid i -> Expr i -> Expr i -> Expr i
exLetVar'  = exLet' . paVar

-- | Constructs a lambda expression, but with a special case:
--
--    @exAbs' x t (exApp (exVar f) (exVar x))  ==  exVar f@
--
-- This eta-contraction is always safe, because f has no effect
exAbs' :: Id i => Patt i -> Type i -> Expr i -> Expr i
exAbs' x t e = case view e of
  ExApp e1 e2 -> case (dataOf x, view e1, view e2) of
    (PaVar y, ExId (J p (Var f)), ExId (J [] (Var y'))) |
      y == y' && J [] y /= J p f
              -> exVar (J p f)
    _         -> exAbs x t e
  _           -> exAbs x t e

-- | Construct an abstraction whose pattern is just a variable.
exAbsVar' :: Id i => Lid i -> Type i -> Expr i -> Expr i
exAbsVar'  = exAbs' . paVar

-- | Construct a type-lambda expression, but with a special case:
--
--   @exTAbs' tv (exTApp (exVar f) tv)  ==  exVar f@
--
-- This should always be safe, because f has no effect
exTAbs' :: Id i => TyVar -> Expr i -> Expr i
exTAbs' tv e = case view e of
  ExTApp e1 t2 -> case (view e1, dataOf t2) of
    (ExId (J p (Var f)), TyVar tv') |
      tv == tv' -> exVar (J p f)
    _           -> exTAbs tv e
  _             -> exTAbs tv e

-- | Does a pattern exactly match an expression?  That is, is
--   @let p = e1 in e@ equivalent to @e1@?  Note that we cannot
--   safely handle data constructors, because they may fail to match.
(-==+) :: Id i => Patt i -> Expr i -> Bool
p -==+ e = case (dataOf p, dataOf e) of
  (PaVar l,      ExId (J [] (Var l')))
    -> l == l'
  (PaCon (J [] (Uid _ "()")) Nothing,
   ExId (J [] (Con (Uid _ "()"))))
    -> True
  (PaPair p1 p2, ExPair e1 e2)
    -> p1 -==+ e1 && p2 -==+ e2
  _ -> False
infix 4 -==+

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

