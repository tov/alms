module Statics.Type (
  tcType, tcTypeRowDots, tcTyPat,
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

-- | Type check a type.
tcType ∷ MonadConstraint tv r m ⇒
         Δ tv → Γ tv → AST.Type R → m (Type tv)
tcType = tcTypeRowDots <-> []

-- | When checking row dots, there are three possible states we could be
--   in:
data DotState tv
  -- | We are not currently under an ellipsis, and the given type
  --   variables are available type variables bound under an ellipsis.
  = Available [tv]
  -- | We are under an ellipsis, but have not found out yet which
  --   variable it protects.
  | Unchosen [tv]
  -- | We are under an ellipsis that controls the given variable,
  --   with the remaining variables available for remaining ellipses.
  | Chosen tv [tv]

-- | Type check a type, resolving dots (maps over rows).  Type variables
--   in the list of dots variables *must not* be bound in the type
--   variable environment.
tcTypeRowDots ∷ MonadConstraint tv r m ⇒
                Δ tv → [(AST.TyVar R, tv)] → Γ tv →
                AST.Type R → m (Type tv)
tcTypeRowDots δ0 dotTVs γ t00 =
  evalStateT (loop δ0 (iaeInit :: CurrentImpArrRule tv) t00)
             (Available dotTVs)
  where
    loop δ iae t0 = withLocation t0 $ case t0 of
      [ty| `$α |] → do
        fvTy <$> δ !.! α `catchAlms` handleDotTV α
      --
      [ty| $t1 -[$opt:mqe]> $t2 |] → do
        qe  ← iaeInterpret (Free <$$> (δ !.!)) iae mqe
        τ1  ← loop δ (iaeLeft iae) t1
        τ2  ← loop δ (iaeRight iae qe τ1) t2
        return (tyFun τ1 qe τ2)
      --
      [ty| $t ... |] → do
        withDots $ loop δ iae t
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

withDots ∷ (MonadSubst tv r m,
            MonadState (DotState (AST.TyVar R, tv)) m) ⇒
           m (Type tv) → m (Type tv)
withDots checkT = do
  dotState ← get
  put . Unchosen =<< case dotState of
    Available [] → do
      typeError' [msg|
        Row dots (<q>...</q>) may only appear on the right-hand side
        of a type operator declaration that also has row dots on the
        left-hand side.
      |]
    Available βs → return βs
    Unchosen βs  → return βs
    Chosen _ βs  → return βs
  σ ← checkT
  dotState' ← get
  case dotState' of
    Available _      → availableBug
    Unchosen _       → unchosenError
    Chosen (_, β') _ → do
      put dotState
      return (TyApp tcRowMap [σ, fvTy β'])
  where
    availableBug  = typeBug "withDots" "Saw Available inside dots"
    unchosenError = do
      typeError' [msg|
        Row dots (<q>...</q>) may only appear on the right-hand side
        of a type operator declaration, and must include in their
        parameter a type variable that appeared under row dots on the
        left-hand side.
      |]

-- | Given a type variable that was not bound in the type variable
--   environment (and the exceptions thrown to reflect that), check
--   if it's involved in row mapping (dots syntax) and if so, translate
--   it thusly.
handleDotTV ∷ (MonadSubst tv r m,
               MonadState (DotState (AST.TyVar R, tv)) m) ⇒
              AST.TyVar R → [AlmsError] → m (Type tv)
handleDotTV α es = do
  dotState ← get
  case dotState of
    Available βs
      | Just _ ← lookup α βs → do
      typeError' [msg|
        Type variable $α matches a row using dot notation (<q>...</q>)
        in the pattern of a type operator, but appears unprotected by
        dots on the right-hand side.
      |]
    Unchosen βs
      | Just α' ← lookup α βs → do
        put (Chosen (α, α') βs)
        return (TyApp tcRowHole [])
    Chosen (β, _) βs
      | α == β               → return (TyApp tcRowHole [])
      | Just _ ← lookup α βs → do
      typeError' [msg|
        Type variable $α, which stands for a row,
        appears under row dots (<q>...</q>) that iterate
        a different row variable, $β.
      |]
    _            → throwAlmsList es

-- | Convert an AST quantifer to an internal quantifier
tcQuant ∷ MonadAlmsError m ⇒ AST.Quant → m Quant
tcQuant AST.Forall        = return Forall
tcQuant AST.Exists        = return Exists
tcQuant (AST.QuantAnti a) = $(AST.antifail)

-- | Type check a type pattern.  Returns the internal pattern and a list
--   of type variables, each specifying whether it is a row variable.
tcTyPat ∷ MonadConstraint tv r m ⇒
          Γ tv → AST.TyPat R → m (TyPat, [(AST.TyVar R, Bool)])
tcTyPat γ = runWriterT . loop where
  loop tp0 = withLocation tp0 $ case tp0 of
    AST.N _ (AST.TpVar tv _)                  → do
      tell [(tv, False)]
      return (TpVar (Here (AST.idName tv)))
    AST.N _ (AST.TpRow tv _)                  → do
      tell [(tv, True)]
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

