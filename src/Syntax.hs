{-# LANGUAGE
      RankNTypes,
      TemplateHaskell,
      TypeFamilies,
      TypeSynonymInstances #-}
-----------------------------------------------------------------------------
-- |
-- This module provides syntax and basic syntax operations for
-- the implementation of the language from the paper "Stateful Contracts
-- for Affine Types".
--
-----------------------------------------------------------------------------

module Syntax (
  -- * Identifiers
  module Syntax.Anti,
  module Syntax.POClass,
  module Syntax.Notable,
  module Syntax.Ident,
  module Syntax.Kind,
  module Syntax.Type,
  module Syntax.Lit,
  module Syntax.Patt,
  module Syntax.Expr,
  module Syntax.Decl,
  module Syntax.SyntaxTable,

  -- * Unfold syntax to lists
  unfoldExAbs, unfoldTyQu, unfoldExTApp, unfoldExApp, unfoldTyFun,
  unfoldTupleExpr, unfoldTuplePatt,

  -- * Miscellany
  module Viewable
) where

import Syntax.Anti
import Syntax.POClass
import Syntax.Notable
import Syntax.Ident
import Syntax.Kind
import Syntax.Type
import Syntax.Lit
import Syntax.Patt
import Syntax.Expr
import Syntax.Decl
import Syntax.SyntaxTable

import Util
import Viewable

deriveAntibles syntaxTable

-- These should be generated:
instance Antible (Prog i) where
  injAnti _ = error "BUG! injAnti: Cannot inject into Prog"
  prjAnti   = const Nothing
  dictOf    = const noAntis

instance Antible Lid where
  injAnti = Lid . injAnti
  prjAnti = prjAnti . unLid
  dictOf  = const lidAntis

instance Antible Uid where
  injAnti = Uid . injAnti
  prjAnti = prjAnti . unUid
  dictOf  = const uidAntis

instance Antible TyVar where
  injAnti = flip TV Qu . injAnti
  prjAnti = prjAnti . tvname
  dictOf  = const tyVarAntis

instance Antible Ident where
  injAnti         = J [] . Var . injAnti
  prjAnti (J [] (Var l)) = prjAnti l
  prjAnti _              = Nothing
  dictOf                 = const idAntis

instance Antible QLid where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const qlidAntis

instance Antible QUid where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const quidAntis

-- Unfolding various sequences

-- | Get the list of formal parameters and body of a
--   lambda/typelambda expression
unfoldExAbs :: Expr i -> ([Either (Patt i, Type i) TyVar], Expr i)
unfoldExAbs  = unscanr each where
  each e = case view e of
    ExAbs x t e' -> Just (Left (x, t), e')
    ExTAbs tv e' -> Just (Right tv, e')
    _            -> Nothing

-- | Get the list of formal parameters and body of a qualified type
unfoldTyQu  :: Quant -> Type i -> ([TyVar], Type i)
unfoldTyQu u = unscanr each where
  each (N _ (TyQu u' x t)) | u == u' = Just (x, t)
  each _                             = Nothing

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
unfoldTyFun :: Type i -> ([Type i], Type i)
unfoldTyFun  = unscanr each where
  each (N _ (TyFun _ ta tr)) = Just (ta, tr)
  each _                     = Nothing

unfoldTupleExpr :: Expr i -> ([Expr i], Expr i)
unfoldTupleExpr  = unscanl each where
  each e = case view e of
    ExPair e1 e2 -> Just (e2, e1)
    _            -> Nothing

unfoldTuplePatt :: Patt i -> ([Patt i], Patt i)
unfoldTuplePatt  = unscanl each where
  each p = case view p of
    PaPair p1 p2 -> Just (p2, p1)
    _            -> Nothing
