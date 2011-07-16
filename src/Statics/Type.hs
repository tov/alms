{-# LANGUAGE
      ParallelListComp,
      QuasiQuotes,
      ScopedTypeVariables,
      TemplateHaskell,
      UnicodeSyntax
    #-}
module Statics.Type (
  tcType
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
        return (tyFun qe τ1 τ2)
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
        αs' ← mapM (\ql → newTV' ql) qls
        τ'  ← loop (δ =+= αs =:*= αs') iae t
        return (closeQuant qu' (zip αs' qls) τ')
      --
      [ty| μ `$α. $t |] → do
        α' ← newTV
        τ' ← loop (δ =+= α =:= α') iae t
        checkGuarded α' τ'
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

_g0 ∷ ∀ tv. Tv tv ⇒ Γ tv
_g0 = mempty
  =+= (AST.ident "int"  :: TypId) =:= tcInt
  =+= (AST.ident "unit" :: TypId) =:= tcUnit
  =+= (AST.ident "*"    :: TypId) =:= tcTuple
  =+= (AST.ident "->"   :: TypId) =:= tcFun
  =+= (AST.ident "()"   :: ConId) =:= (Left tcUnit
                                         ∷ Either TyCon
                                                  (Maybe (Type tv)))
  =+= (AST.ident "x"    :: VarId) =:= (tyInt ∷ Type tv)

