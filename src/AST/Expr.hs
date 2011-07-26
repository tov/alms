module AST.Expr (
  -- * Expressions
  Expr'(..), Expr, ExprNote(..), newExpr,
  -- ** Letrec and case
  Binding'(..), Binding, newBinding,
  CaseAlt'(..), CaseAlt, newCaseAlt,
  Field'(..), Field, newField,

  -- * Two-level expression constructors
  -- | These fill in the source location field based on the
  -- subexpressions and perform the free variable analysis
  -- | variables
  exVar, exLit, exCon, exLet, exCase, exLetRec, exLetDecl,
  exPair, exAbs, exApp, exInj, exEmb, exCast, exRec, exSel, exAnti,

  caClause, caPrj, caAnti,
  bnBind, bnAnti,
  fdField, fdAnti,
  -- ** Synthetic expression constructors
  exBVar, exBCon,
  exChar, exStr, exInt, exFloat,
  exSeq,
  exUnit, exNilRecord,
  exNil, exCons,
  ToExpr(..),

  -- * Expression accessors and updaters
  syntacticValue, isAnnotated, getExprAnnot, cafakepatt,
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
type Field i   = N (ExprNote i) (Field' i)

-- | The underlying expression type, which we can pattern match without
-- dealing with the common fields above.
data Expr' i
  -- | variables
  = ExVar (QVarId i)
  -- | literals
  | ExLit Lit
  -- | data construction
  | ExCon (QConId i) (Maybe (Expr i))
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
  -- | record extension
  --   (@True@ means additive rather than multiplicative records)
  | ExRec Bool [Field i] (Expr i)
  -- | record lookup
  | ExSel (Expr i) (Uid i)
  -- | dynamic promotion (True) or static type ascription (False)
  | ExCast (Expr i) (Type i) Bool
  -- | antiquotes
  | ExAnti Anti
  deriving (Typeable, Data)

-- | Let-rec bindings require us to give types
data Binding' i
  = BnBind {
      bnvar  :: VarId i,
      bnexpr :: Expr i
    }
  | BnAnti Anti
  deriving (Typeable, Data)

data CaseAlt' i
  -- | Normal match clauses
  = CaClause {
      capatt :: Patt i,
      caexpr :: Expr i
    }
  -- | Open variant elimination
  | CaPrj {
      calab   :: Uid i,
      campatt :: Maybe (Patt i),
      caexpr  :: Expr i
    }
  -- | Antiquote
  | CaAnti Anti
  deriving (Typeable, Data)

data Field' i
  -- | Normal match clauses
  = FdField {
      fdsel  :: Uid i,
      fdexpr :: Expr i
    }
  -- | Antiquote
  | FdAnti Anti
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
instance Tag i => Fv (N (ExprNote i) a) i where fv = efv_ . noteOf

instance Dv (N (ExprNote i) (Binding' i)) i where
  dv (N _ (BnBind f _)) = [f]
  dv (N _ (BnAnti _))   = []

instance Notable (ExprNote i) where
  newNote = ExprNote {
    eloc_  = bogus,
    efv_   = M.empty
  }

newExpr :: Tag i => Expr' i -> Expr i
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
                  pot = fv e2 |*| fv bns
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
  ExRec True flds e2 ->
    newNote {
      efv_  = fv (ADDITIVE flds) |*| fv e2,
      eloc_ = getLoc (flds, e2)
    }
  ExRec False flds e2 ->
    newNote {
      efv_  = fv flds |*| fv e2,
      eloc_ = getLoc (flds, e2)
    }
  ExSel e1 _ ->
    newNote {
      efv_  = fv e1,
      eloc_ = getLoc e1
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

newBinding :: Tag i => Binding' i -> Binding i
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

newCaseAlt :: Tag i => CaseAlt' i -> CaseAlt i
newCaseAlt ca0 = flip N ca0 $ case ca0 of
  CaClause x e ->
    newNote {
      efv_  = fv e |--| qdv x,
      eloc_ = getLoc (x, e)
    }
  CaPrj _ mx e ->
    newNote {
      efv_  = fv e |--| qdv mx,
      eloc_ = getLoc (mx, e)
    }
  CaAnti a ->
    newNote {
      efv_  = antierror "fv" a
    }

newField :: Tag i => Field' i -> Field i
newField f0 = flip N f0 $ case f0 of
  FdField _ e ->
    newNote {
      efv_  = fv e,
      eloc_ = getLoc e
    }
  FdAnti a ->
    newNote {
      efv_  = antierror "fv" a
    }

deriveNotable 'newExpr    (''Tag, [0]) ''Expr
deriveNotable 'newCaseAlt (''Tag, [0]) ''CaseAlt
deriveNotable 'newBinding (''Tag, [0]) ''Binding
deriveNotable 'newField   (''Tag, [0]) ''Field

exBVar :: Tag i => VarId i -> Expr i
exBVar  = exVar . J []

exBCon :: Tag i => ConId i -> Maybe (Expr i) -> Expr i
exBCon  = exCon . J []

exChar :: Tag i => Char -> Expr i
exChar = exLit . LtChar

exStr :: Tag i => String -> Expr i
exStr  = exLit . LtStr

exInt :: (Tag i, Integral a) => a -> Expr i
exInt  = exLit . LtInt . toInteger

exFloat :: Tag i => Double -> Expr i
exFloat  = exLit . LtFloat

exSeq :: Tag i => Expr i -> Expr i -> Expr i
exSeq e1 e2 = exLet paWild e1 e2

exUnit, exNilRecord :: Tag i => Expr i
exUnit      = exCon idUnitVal Nothing
exNilRecord = exVar idNilRecord

exCons :: Tag i => Expr i -> Expr i -> Expr i
exCons = exCon idConsList . Just <$$> exPair

exNil :: Tag i => Expr i
exNil  = exCon idNilList Nothing

class ToExpr a i | a → i where
  toExpr ∷ a → Expr i

instance ToExpr (Expr i) i where
  toExpr = id

instance Tag i ⇒ ToExpr (QVarId i) i where
  toExpr = exVar

instance Tag i ⇒ ToExpr (VarId i) i where
  toExpr = exBVar

instance (Tag i, ToExpr a i, ToExpr b i) ⇒ ToExpr (a, b) i where
  toExpr (a, b) = exPair (toExpr a) (toExpr b)

instance Tag i ⇒ ToExpr String i where
  toExpr = exStr

instance Tag i ⇒ ToExpr Int i where
  toExpr = exInt

instance Tag i ⇒ ToExpr Char i where
  toExpr = exChar

instance Tag i ⇒ ToExpr Double i where
  toExpr = exFloat

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
  ExRec b flds e2
                 → b ||
                   (and [ syntacticValue ei | FdField _ ei ← view <$> flds ]
                    && syntacticValue e2)
  ExSel _ _      → False
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
      CaPrj    { caexpr = e' } → isAnnotated e'
      CaAnti a                 → antierror "isAnnotated" a
  ExLetRec _ e2  → isAnnotated e2
  ExLetDecl _ e2 → isAnnotated e2
  ExPair _ _     → False
  ExAbs _ _      → False
  ExApp _ _      → False
  ExInj _ _      → False
  ExEmb _ _      → False
  ExRec _ _ _    → False
  ExSel _ _      → False
  ExCast _ _ _   → True
  ExAnti a       → antierror "syntacticValue" a

-- | Get the (static) type annotation on an expression
getExprAnnot ∷ Expr i → Maybe (Type i)
getExprAnnot e0 = case view e0 of
  ExCast _ annot False → Just annot
  _                    → Nothing

-- | Given a case alternative, produce a (potentially fake)
--   representation of its pattern, suitable for printing.
cafakepatt ∷ Tag i ⇒ CaseAlt i → Patt i
cafakepatt ca0 = case view ca0 of
  CaClause x _ → x
  CaPrj u mx _ → paCon (qident ('#':idName u)) mx
  CaAnti a     → $antierror
