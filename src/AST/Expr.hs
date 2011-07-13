{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      TemplateHaskell,
      TypeFamilies,
      TypeSynonymInstances,
      UnicodeSyntax #-}
module AST.Expr (
  -- * Expressions
  Expr'(..), Expr, ExprNote(..), newExpr,
  -- ** Letrec and case
  Binding'(..), Binding, newBinding,
  CaseAlt'(..), CaseAlt, newCaseAlt,

  -- * Two-level expression constructors
  -- | These fill in the source location field based on the
  -- subexpressions and perform the free variable analysis
  -- | variables
  exVar, exLit, exCon, exLet, exCase, exLetRec, exLetDecl,
  exPair, exAbs, exApp, exInj, exEmb, exCast, exAnti,

  caClause, caAnti,
  bnBind, bnAnti,
  -- ** Synthetic expression constructors
  exId, exBVar, exBCon,
  exChar, exStr, exInt, exFloat,
  exSeq,
  -- ** Optimizing expression constructors
  exLet', exLetVar', exAbs', exAbsVar',

  -- * Expression accessors and updaters
  syntacticValue, isAnnotated,
) where

import Util
import AST.Notable
import AST.Anti
import AST.Ident
import AST.Type
import AST.Lit
import AST.Patt
import {-# SOURCE #-} AST.Decl

import Meta.DeriveNotable

import Prelude ()
import Data.Generics (Typeable(..), Data(..))
import qualified Data.Map as M

type Expr i    = N (ExprNote i) (Expr' i)
type Binding i = N (ExprNote i) (Binding' i)
type CaseAlt i = N (ExprNote i) (CaseAlt' i)

-- | The underlying expression type, which we can pattern match without
-- dealing with the common fields above.
data Expr' i
  -- | variables
  = ExVar (QLid i)
  -- | literals
  | ExLit Lit
  -- | data construction
  | ExCon (QUid i) (Maybe (Expr i))
  -- | let expressions
  | ExLet (Patt i) (Expr i) (Expr i)
  -- | case expressions (including desugared @if@)
  | ExCase (Expr i) [CaseAlt i]
  -- | recursive let expressions
  | ExLetRec [Binding i] (Expr i)
  -- | nested declarations
  | ExLetDecl (Decl i) (Expr i)
  -- | pair construction
  | ExPair (Expr i) (Expr i)
  -- | lambda
  | ExAbs (Patt i) (Expr i)
  -- | application
  | ExApp (Expr i) (Expr i)
  -- | open variant construction
  | ExInj (Uid i) (Maybe (Expr i))
  -- | open variant embedding
  | ExEmb (Uid i) (Expr i)
  -- | dynamic promotion (True) or static type ascription (False)
  | ExCast (Expr i) (Type i) Bool
  -- | antiquotes
  | ExAnti Anti
  deriving (Typeable, Data)

-- | Let-rec bindings require us to give types
data Binding' i
  = BnBind {
      bnvar  :: Lid i,
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
  ExVar v ->
    newNote {
      efv_ = M.singleton v 1
    }
  ExLit _ -> newNote
  ExCon _ me2 ->
    newNote {
      efv_  = fv me2,
      eloc_ = getLoc me2
    }
  ExLet x1 e2 e3 ->
    newNote {
      efv_  = fv e2 |*| (fv e3 |--| qdv x1),
      eloc_ = getLoc (x1, e2, e3)
    }
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
  ExAbs p1 e2 ->
    newNote {
      efv_  = fv e2 |--| qdv p1,
      eloc_ = getLoc (p1, e2)
    }
  ExApp e1 e2 ->
    newNote {
      efv_  = fv e1 |*| fv e2,
      eloc_ = getLoc (e1, e2)
    }
  ExInj _ me2 ->
    newNote {
      efv_  = fv me2,
      eloc_ = getLoc me2
    }
  ExEmb _ e2 ->
    newNote {
      efv_  = fv e2,
      eloc_ = getLoc e2
    }
  ExCast e1 t2 _ ->
    newNote {
      efv_  = fv e1,
      eloc_ = getLoc (e1, t2)
    }
  ExAnti a ->
    newNote {
      efv_  = antierror "fv" a
    }

newBinding :: Id i => Binding' i -> Binding i
newBinding b0 = flip N b0 $ case b0 of
  BnBind x e ->
    newNote {
      efv_  = fv e |-| J [] x,
      eloc_ = getLoc e
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

exId   :: Id i => Ident i -> Expr i
exId    = (exVar ||| exCon <-> Nothing) . view

exBVar :: Id i => Lid i -> Expr i
exBVar  = exVar . J []

exBCon :: Id i => Uid i -> Maybe (Expr i) -> Expr i
exBCon  = exCon . J []

exChar :: Id i => Char -> Expr i
exChar = exLit . LtChar

exStr :: Id i => String -> Expr i
exStr  = exLit . LtStr

exInt :: (Id i, Integral a) => a -> Expr i
exInt  = exLit . LtInt . toInteger

exFloat :: Id i => Double -> Expr i
exFloat  = exLit . LtFloat

exSeq :: Id i => Expr i -> Expr i -> Expr i
exSeq e1 e2 = exLet paWild e1 e2

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
--    @exAbs' x     (exApp (exVar f) x)      ==  exVar f@
--    @exAbs' (x,y) (exApp (exVar f) (x,y))  ==  exVar f@
--
-- This eta-contraction is always safe, because f has no effect
exAbs' :: Id i => Patt i -> Expr i -> Expr i
exAbs' x e = case view e of
  ExApp e1 e2 -> case view e1 of
    ExVar (J p f) | x -==+ e2
              -> exVar (J p f)
    _         -> exAbs x e
  _           -> exAbs x e

-- | Construct an abstraction whose pattern is just a variable.
exAbsVar' :: Id i => Lid i -> Expr i -> Expr i
exAbsVar'  = exAbs' . paVar

-- | Does a pattern exactly match an expression?  That is, is
--   @let p = e1 in e@ equivalent to @e1@?  Note that we cannot
--   safely handle data constructors, because they may fail to match.
(-==+) :: Id i => Patt i -> Expr i -> Bool
p -==+ e = case (dataOf p, dataOf e) of
  (PaVar l,      ExVar (J [] l'))
    -> l == l'
  (PaCon (J [] (Uid _ "()")) Nothing,
   ExCon (J [] (Uid _ "()")) Nothing)
    -> True
  (PaPair p1 p2, ExPair e1 e2)
    -> p1 -==+ e1 && p2 -==+ e2
  _ -> False
infix 4 -==+

-- | Is the expression conservatively side-effect free?
syntacticValue :: Expr i -> Bool
syntacticValue e = case view e of
  ExVar _        → True
  ExLit _        → True
  ExCon _ me     → maybe True syntacticValue me
  ExLet _ e1 e2  → syntacticValue e1 && syntacticValue e2
  ExCase _ _     → False
  ExLetRec bs e2 → all eachBinding bs && syntacticValue e2 where
    eachBinding bn = case view bn of
      BnBind { bnexpr = e' } → syntacticValue e'
      BnAnti a               → antierror "syntacticValue" a
  ExLetDecl _ _  → False
  ExPair e1 e2   → syntacticValue e1 && syntacticValue e2
  ExAbs _ _      → True
  ExApp _ _      → False
  ExInj _ me     → maybe True syntacticValue me
  ExEmb _ e1     → syntacticValue e1
  ExCast e1 _ b  → syntacticValue e1 && not b
  ExAnti a       → antierror "syntacticValue" a

-- | Is the expression annotated with a type ascription or dynamic cast?
isAnnotated ∷ Expr i → Bool
isAnnotated e = case view e of
  ExVar _        → False
  ExLit _        → False
  ExCon _ _      → False
  ExLet _ _ e2   → isAnnotated e2
  ExCase _ cs    → all eachClause cs where
    eachClause c = case view c of
      CaClause { caexpr = e' } → isAnnotated e'
      CaAnti a                 → antierror "isAnnotated" a
  ExLetRec _ e2  → isAnnotated e2
  ExLetDecl _ e2 → isAnnotated e2
  ExPair _ _     → False
  ExAbs _ _      → False
  ExApp _ _      → False
  ExInj _ _      → False
  ExEmb _ _      → False
  ExCast _ _ _   → True
  ExAnti a       → antierror "syntacticValue" a

