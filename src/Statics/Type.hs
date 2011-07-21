module Statics.Type (
  tcType, tcTyPat,
) where

import Util
import qualified AST
import Meta.Quasi
import Type
import Statics.Env
import Statics.Error
import Statics.Constraint

import Prelude ()
import qualified Data.Map as M

tcType ∷ MonadConstraint tv r m ⇒
         Δ tv → Γ tv → AST.Type R → m (Type tv)
tcType δ0 γ = loop δ0 (iaeInit :: CurrentImpArrRule tv)
  where
    loop δ iae t0 = withLocation t0 $ case t0 of
      [ty| `$α |] → do
        fvTy <$> δ !.! α
      --
      [ty| $t1 -[$opt:mqe]> $t2 |] → do
        qe  ← iaeInterpret (Free <$$> (δ !.!)) iae mqe
        τ1  ← loop δ (iaeLeft iae) t1
        τ2  ← loop δ (iaeRight iae qe τ1) t2
        return (tyFun τ1 qe τ2)
      --
      [ty| ($list:ts) $qtid:n |] → do
        tc  ← γ !.! n
        τs  ← zipWithM (loop δ . iaeUnder iae) (tcArity tc) ts
        zipWithM_ (⊏:) τs (tcBounds tc)
        checkLength (length ts) (length (tcArity tc))
        return (TyApp tc τs)
        where
        checkLength actual expected =
          tAssExp (actual == expected)
            [msg| Type constructor $q:n got the wrong number of parameters: |]
            [msg| $actual |]
            [msg| $expected |]
      --
      [ty| $quant:qu `$_. $_ |] → do
        let (αs, t) = AST.unfoldTyQu qu t0
            qls     = AST.tvqual <$> αs
        qu' ← tcQuant qu
        αs' ← mapM (curry newTV' Skolem) qls
        τ'  ← loop (δ =+= αs =:*= αs') iae t
        return (closeQuant qu' (zip αs' qls) τ')
      --
      [ty| μ `$α. $t |] → do
        α' ← newTV
        τ' ← loop (δ =+= α =:= α') iae t
        checkGuarded α' τ'
        τ' ⊏: fvTy α'
        return (closeRec α' τ')
        where
        checkGuarded α' τ' = case M.lookup α' (ftvG τ') of
          Just False
            → typeError [msg|
                Recursive type is ill formed because the bound variable
                is unguarded:
                <dl>
                  <dt>type:     <dd>$t0
                  <dt>variable: <dd>$α
                </dl>
                The type variable bound by μ must appear only under type
                constructors that are allowed to <q>guard</q> recursion,
                such as under an open variant.
              |]
          _ → return ()
      --
      [ty| `$uid:uid of $t1 | $t2 |] → do
        τ1 ← loop δ iae t1
        τ2 ← loop δ iae t2
        return (TyRow uid τ1 τ2)
      --
      [ty| $anti:a |] → $(AST.antifail)

-- | Convert an AST quantifer to an internal quantifier
tcQuant ∷ MonadAlmsError m ⇒ AST.Quant → m Quant
tcQuant AST.Forall        = return Forall
tcQuant AST.Exists        = return Exists
tcQuant (AST.QuantAnti a) = $(AST.antifail)

-- | Type check a type pattern
tcTyPat ∷ MonadConstraint tv r m ⇒
          Γ tv → AST.TyPat R → m (TyPat, [AST.TyVar R])
tcTyPat γ = runWriterT . loop where
  loop tp0 = withLocation tp0 $ case tp0 of
    AST.N _ (AST.TpVar tv _)                  → do
      tell [tv]
      return (TpVar (Here (AST.idName tv)))
    AST.N _ (AST.TpRow tv _)                  → do
      tell [tv]
      return (TpRow (Here (AST.idName tv)))
    [tpQ| ($list:tps) $qtid:n |]              → do
      tc ← γ !.! n
      tassert (isNothing (tcNext tc)) $
        [msg| In type operator pattern, the type constructor to
              be matched is also a type operator:
              <dl>
                <dt>In pattern:       <dd> $tp0
                <dt>Type constructor: <dd> $1
              </dl>
              Type constructors in type patterns must be abstract types
              or concrete data types, not type synonyms or operators.
        |] (tcName tc)
      TpApp tc <$> mapM loop tps
    [tpQ| $antiP:a |]                     → $(AST.antifail)

