{-# LANGUAGE
      FlexibleInstances,
      FunctionalDependencies,
      MultiParamTypeClasses,
      ParallelListComp,
      QuasiQuotes,
      TemplateHaskell,
      UndecidableInstances,
      UnicodeSyntax
      #-}
-- | For treating syntactic types as type annotations.
module AST.TypeAnnotation (
  Annot, HasAnnotations(..),
) where

import Util
import AST
import AST.Patt
import Meta.Quasi

import Prelude ()
import qualified Data.Map as M
import qualified Data.Set as S

-- | A type annotation is merely a syntactic type
type Annot i = Type i

-- | Find out the free variables of a type annotation.  Minimal
--   definition: @annotFtvMapM@
class Tag i ⇒ HasAnnotations a i | a → i where
  -- | The previous method, specialized to return a map.
  annotFtvMapM  ∷ (Monad m, Monoid r) ⇒
                  (TyVar i → m r) →
                  (QTypId i → Int → r → m r) →
                  a →
                  m (M.Map (TyVar i) r)

  -- | A pure version of the previous method.
  annotFtvMap   ∷ Monoid r ⇒
                  (TyVar i → r) →
                  (QTypId i → Int → r → r) →
                  a →
                  (M.Map (TyVar i) r)
  annotFtvMap var con =
    runIdentity . annotFtvMapM (return <$> var)
                               (return <$$$> con)

  -- | Just the set of type variables, please.
  annotFtvSet   ∷ a → S.Set (TyVar i)
  annotFtvSet   = M.keysSet . annotFtvMap (\_ → ()) (\_ _ () → ())

-- | Shorter-named alias
afm ∷ (HasAnnotations a i, Monad m, Monoid r) ⇒
      (TyVar i → m r) →
      (QTypId i → Int → r → m r) →
      a →
      m (M.Map (TyVar i) r)
afm = annotFtvMapM

--
-- Generic instances
--

instance (HasAnnotations a i, HasAnnotations b i) ⇒
         HasAnnotations (a, b) i where
  annotFtvMapM var con (a, b) =
    M.unionWith mappend `liftM` afm var con a `ap` afm var con b

instance (HasAnnotations a i, HasAnnotations b i, HasAnnotations c i) ⇒
         HasAnnotations (a, b, c) i where
  annotFtvMapM var con (a, b, c) = afm var con (a, (b, c))

instance HasAnnotations a i ⇒ HasAnnotations [a] i where
  annotFtvMapM var con = liftM fold . mapM (afm var con)

instance HasAnnotations a i ⇒ HasAnnotations (Maybe a) i where
  annotFtvMapM var con = liftM fold . mapM (afm var con)

instance HasAnnotations a i ⇒ HasAnnotations (N note a) i where
  annotFtvMapM = afm <$$.> dataOf

--
-- Specific instances for syntax.
--

instance Tag i ⇒ HasAnnotations (TyVar i) i where
  annotFtvMapM _   _ (TVAnti a) = $antifail
  annotFtvMapM var _ tv         = M.singleton tv `liftM` var tv

instance Tag i ⇒ HasAnnotations (QExp' i) i where
  annotFtvMapM var con qe0 = case qe0 of
    [qeQ|' $qlit:_   |]           → return mempty
    [qeQ|'  '$tv |]               → afm var con tv
    [qeQ|' $qe1 ⋁ $qe2 |]         → afm var con (qe1, qe2)
    [qeQ|' $anti:a |]             → $antierror

instance Tag i ⇒ HasAnnotations (Type' i) i where
  annotFtvMapM var con t0 = case t0 of
    [ty|' ($list:ts) $qtid:ql |]  →
      fold `liftM` sequence
        [ mapM (con ql ix) =<< afm var con t
        | t  ← ts
        | ix ← [ 1 .. ] ]
    [ty|'  '$tv |]                → afm var con tv
    [ty|' $t1 -[$opt:qe]> $t2 |]  → do
      t1m ← mapM (con (qident "->") 1) =<< afm var con t1
      qem ← mapM (con (qident "->") 2) =<< afm var con qe
      t2m ← mapM (con (qident "->") 3) =<< afm var con t2
      return (t1m `mappend` qem `mappend` t2m)
    [ty|' $quant:_ '$tv. $t |]    → M.delete tv `liftM` afm var con t
    [ty|' μ '$tv. $t |]           → M.delete tv `liftM` afm var con t
    [ty|' `$uid:_ of $t1 | $t2 |] → afm var con (t1, t2)
    [ty|' $anti:a |]              → $antifail

instance Tag i => HasAnnotations (Patt' i) i where
  annotFtvMapM var con x0 = case x0 of
    [pa|' _ |]                  → return mempty
    [pa|' $lid:_ |]             → return mempty
    [pa|' $qcid:_ $opt:mx |]    → afm var con mx
    [pa|' ($x, $y) |]           → afm var con (x, y)
    [pa|' $lit:_ |]             → return mempty
    [pa|' $x as $vid:_ |]       → afm var con x
    [pa|' `$uid:_ $opt:mx |]    → afm var con mx
    [pa|' $x : $t |]            → afm var con (x, t)
    [pa|' ! $x |]               → afm var con x
    [pa|' $anti:a |]            → $antifail

instance Tag i ⇒ HasAnnotations (Expr' i) i where
  annotFtvMapM var con e0 = case e0 of
    [ex|' $qvid:_ |]            → return mempty
    [ex|' $lit:_ |]             → return mempty
    [ex|' $qcid:_ $opt:me |]    → afm var con me
    [ex|' let $x = $e in $e' |] → afm var con (x, e, e')
    [ex|' match $e with $list:cas |]
                                → afm var con (e, cas)
    [ex|' let rec $list:bns in $e |]
                                → afm var con (bns, e)
    [ex|' let $decl:_ in $e |]  → afm var con e
    [ex|' ($e1, $e2) |]         → afm var con (e1, e2)
    [ex|' λ $x → $e |]          → afm var con (x, e)
    [ex|' $e1 $e2 |]            → afm var con (e1, e2)
    [ex|' `$uid:_ $opt:me |]    → afm var con me
    [ex|' #$uid:_ $e |]         → afm var con e
    [ex|' $e : $t |]            → afm var con (e, t)
    [ex|' $e :> $t |]           → afm var con (e, t)
    [ex|' $anti:a |]            → $antifail

instance Tag i ⇒ HasAnnotations (CaseAlt' i) i where
  annotFtvMapM var con ca0 = case ca0 of
    [caQ|' $x → $e |]           → afm var con (x, e)
    [caQ|' $antiC:a |]          → $antifail

instance Tag i ⇒ HasAnnotations (Binding' i) i where
  annotFtvMapM var con bn0 = case bn0 of
    [bnQ|' $lid:_ = $e |]       → afm var con  e
    [bnQ|' $antiB:a |]          → $antifail

