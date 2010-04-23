-----------------------------------------------------------------------------
-- |
-- This module provides syntax and basic syntax operations for
-- the implementation of the language from the paper "Stateful Contracts
-- for Affine Types".
--
-----------------------------------------------------------------------------

module Syntax (
  -- * Identifiers
  module Syntax.POClass,
  module Syntax.Kind,
  module Syntax.Ident,
  module Syntax.Type,
  module Syntax.Patt,
  module Syntax.Expr,
  module Syntax.Decl,

  -- * Unfold syntax to lists
  unfoldExAbs, unfoldTyQu, unfoldExTApp, unfoldExApp, unfoldTyFun,
  unfoldTupleExpr, unfoldTuplePatt,

  -- * Miscellany
  module Viewable
) where

import Syntax.POClass
import Syntax.Kind
import Syntax.Ident
import Syntax.Type
import Syntax.Patt
import Syntax.Expr
import Syntax.Decl

import Util
import Viewable

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
