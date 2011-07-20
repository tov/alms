-----------------------------------------------------------------------------
-- |
-- This module provides abstract syntax and basic syntax operations.
--
-----------------------------------------------------------------------------

module AST (
  module AST.Anti,
  module AST.Notable,
  module AST.Ident,
  module AST.Kind,
  module AST.Type,
  module AST.Lit,
  module AST.Patt,
  module AST.Expr,
  module AST.Decl,
  module AST.SyntaxTable,
  module Data.Lattice,

  -- * Unfold syntax to lists
  unfoldExAbs, unfoldTyQu, unfoldTyMu, unfoldTyRow,
  unfoldExApp, unfoldTyFun,
  unfoldTupleExpr, unfoldTuplePatt, unfoldSeWith,
) where

import Prelude ()

import AST.Anti
import AST.Notable
import AST.Ident
import AST.Kind
import AST.Type
import AST.Lit
import AST.Patt
import AST.Expr
import AST.Decl
import AST.SyntaxTable
import Data.Lattice

import Util

deriveAntibles syntaxTable

instance Antible (Prog i) where
  injAnti _ = error "BUG! injAnti: Cannot inject into Prog"
  prjAnti   = const Nothing
  dictOf    = const noAntis

-- These should be generated:
instance Antible (Ident i) where
  injAnti                = J [] . Var . injAnti
  prjAnti (J [] (Var l)) = prjAnti l
  prjAnti _              = Nothing
  dictOf                 = const idAntis

instance Antible (QLid i) where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const qlidAntis

instance Antible (QUid i) where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const quidAntis

instance Antible (QTypId i) where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const qtypIdAntis

instance Antible (QVarId i) where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const qvarIdAntis

instance Antible (QConId i) where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const qconIdAntis

instance Antible (QModId i) where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const qmodIdAntis

instance Antible (QSigId i) where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const qsigIdAntis

-- Unfolding various sequences

-- | Get the list of formal parameters and body of a
--   lambda/typelambda expression
unfoldExAbs :: Expr i -> ([Patt i], Expr i)
unfoldExAbs  = unscanr each where
  each e = case view e of
    ExAbs x e' -> Just (x, e')
    _          -> Nothing

-- | Get the list of formal parameters and body of a qualified type
unfoldTyQu  :: Quant -> Type i -> ([TyVar i], Type i)
unfoldTyQu u = unscanr each where
  each (N _ (TyQu u' x t)) | u == u' = Just (x, t)
  each _                             = Nothing

-- | Get the list of mu-bound tvs of a recursive type
unfoldTyMu  :: Type i -> ([TyVar i], Type i)
unfoldTyMu = unscanr each where
  each (N _ (TyMu x t)) = Just (x, t)
  each _                = Nothing

-- | Get the list of labels and types in a row type
unfoldTyRow :: Type i -> ([(Uid i, Type i)], Type i)
unfoldTyRow = unscanr each where
  each (N _ (TyRow i t1 t2)) = Just ((i, t1), t2)
  each _                     = Nothing

-- | Get the list of actual parameters and body of a value application
unfoldExApp :: Expr i -> ([Expr i], Expr i)
unfoldExApp  = unscanl each where
  each e = case view e of
    ExApp e1 e2 -> Just (e2, e1)
    _           -> Nothing

-- | Get the list of argument types and result type of a function type
unfoldTyFun :: Type i -> ([Type i], Type i)
unfoldTyFun  = unscanr each where
  each (N _ (TyFun ta _ tr)) = Just (ta, tr)
  each _                     = Nothing

-- | Get the elements of a tuple as a list
unfoldTupleExpr :: Expr i -> ([Expr i], Expr i)
unfoldTupleExpr  = unscanl each where
  each e = case view e of
    ExPair e1 e2 -> Just (e2, e1)
    _            -> Nothing

-- | Get the elements of a tuple pattere as a list
unfoldTuplePatt :: Patt i -> ([Patt i], Patt i)
unfoldTuplePatt  = unscanl each where
  each p = case view p of
    PaPair p1 p2 -> Just (p2, p1)
    _            -> Nothing

-- | Get all the "with type" clauses on a signature expression
unfoldSeWith :: SigExp i -> ([(QTypId i, [TyVar i], Type i)], SigExp i)
unfoldSeWith  = unscanl each where
  each p = case view p of
    SeWith se ql tvs t -> Just ((ql, tvs, t), se)
    _                  -> Nothing
