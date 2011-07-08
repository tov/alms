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
module TypeAnnotation (
  Annot, HasAnnotations(..),
) where

import Util
import Syntax
import Meta.Quasi

import Prelude ()
import qualified Data.Map as M
import qualified Data.Set as S

-- | A type annotation is merely a syntactic type
type Annot i = Type i

-- | Find out the free variables of a type annotation.  Minimal
--   definition: @annotFtvMapM@
class Id i ⇒ HasAnnotations a i | a → i where
  -- | The previous method, specialized to return a map.
  annotFtvMapM  ∷ (Monad m, Monoid r) ⇒
                  (QLid i → Int → r → m r) →
                  a →
                  m (M.Map (TyVar i) r)

  -- | A pure version of the previous method.
  annotFtvMap   ∷ Monoid r ⇒
                  (QLid i → Int → r → r) →
                  a →
                  (M.Map (TyVar i) r)
  annotFtvMap con = runIdentity . annotFtvMapM (return <$$$> con)

  -- | Just the set of type variables, please.
  annotFtvSet   ∷ a → S.Set (TyVar i)
  annotFtvSet   = M.keysSet . annotFtvMap (\_ _ () → ())

-- | Shorter-named alias
afm ∷ (HasAnnotations a i, Monad m, Monoid r) ⇒
      (QLid i → Int → r → m r) →
      a →
      m (M.Map (TyVar i) r)
afm = annotFtvMapM

--
-- Generic instances
--

instance (HasAnnotations a i, HasAnnotations b i) ⇒
         HasAnnotations (a, b) i where
  annotFtvMapM con (a, b) =
    mappend `liftM` afm con a `ap` afm con b

instance (HasAnnotations a i, HasAnnotations b i, HasAnnotations c i) ⇒
         HasAnnotations (a, b, c) i where
  annotFtvMapM con (a, b, c) = afm con (a, (b, c))

instance HasAnnotations a i ⇒ HasAnnotations [a] i where
  annotFtvMapM con = liftM fold . mapM (afm con)

instance HasAnnotations a i ⇒ HasAnnotations (Maybe a) i where
  annotFtvMapM con = liftM fold . mapM (afm con)

instance HasAnnotations a i ⇒ HasAnnotations (N note a) i where
  annotFtvMapM = afm <$.> dataOf

--
-- Specific instances for syntax.
--

instance Id i ⇒ HasAnnotations (TyVar i) i where
  annotFtvMapM _ (TVAnti a) = $antifail
  annotFtvMapM _ tv         = return (M.singleton tv mempty)

instance Id i ⇒ HasAnnotations (QExp' i) i where
  annotFtvMapM con qe0 = case qe0 of
    [qeQ|' $qlit:_   |]           → return mempty
    [qeQ|'  '$tv |]               → afm con tv
    [qeQ|' $qe1 ⋁ $qe2 |]         → afm con (qe1, qe2)
    [qeQ|' $anti:a |]             → $antierror

instance Id i ⇒ HasAnnotations (Type' i) i where
  annotFtvMapM con t0 = case t0 of
    [ty|' ($list:ts) $qlid:ql |]  →
      fold `liftM` sequence
        [ mapM (con ql ix) =<< afm con t
        | t  ← ts
        | ix ← [ 1 .. ] ]
    [ty|'  '$tv |]                → afm con tv
    [ty|' $t1 -[$opt:qe]> $t2 |]  → do
      t1m ← mapM (con (qlid "->") 1) =<< afm con t1
      qem ← mapM (con (qlid "->") 2) =<< afm con qe
      t2m ← mapM (con (qlid "->") 3) =<< afm con t2
      return (t1m `mappend` qem `mappend` t2m)
    [ty|' $quant:_ '$tv. $t |]    → M.delete tv `liftM` afm con t
    [ty|' μ '$tv. $t |]           → M.delete tv `liftM` afm con t
    [ty|' `$uid:_ of $t1 | $t2 |] → afm con (t1, t2)
    [ty|' $anti:a |]              → $antifail

instance Id i => HasAnnotations (Patt' i) i where
  annotFtvMapM con x0 = case x0 of
    [pa|' _ |]                  → return mempty
    [pa|' $lid:_ |]             → return mempty
    [pa|' $quid:_ $opt:mx |]    → afm con mx
    [pa|' ($x, $y) |]           → afm con (x, y)
    [pa|' $lit:_ |]             → return mempty
    [pa|' $x as $lid:_ |]       → afm con x
    [pa|' `$uid:_ $opt:mx |]    → afm con mx
    [pa|' $x : $t |]            → afm con (x, t)
    [pa|' ! $x |]               → afm con x
    [pa|' $anti:a |]            → $antifail

instance Id i ⇒ HasAnnotations (Expr' i) i where
  annotFtvMapM con e0 = case e0 of
    [ex|' $qlid:_ |]            → return mempty
    [ex|' $lit:_ |]             → return mempty
    [ex|' $quid:_ $opt:me |]    → afm con me
    [ex|' let $x = $e in $e' |] → afm con (x, e, e')
    [ex|' match $e with $list:cas |]
                                → afm con (e, cas)
    [ex|' let rec $list:bns in $e |]
                                → afm con (bns, e)
    [ex|' let $decl:_ in $e |]  → afm con e
    [ex|' ($e1, $e2) |]         → afm con (e1, e2)
    [ex|' λ $x → $e |]          → afm con (x, e)
    [ex|' $e1 $e2 |]            → afm con (e1, e2)
    [ex|' `$uid:_ $opt:me |]    → afm con me
    [ex|' #$uid:_ $e |]         → afm con e
    [ex|' $e : $t |]            → afm con (e, t)
    [ex|' $e :> $t |]           → afm con (e, t)
    [ex|' $anti:a |]            → $antifail

instance Id i ⇒ HasAnnotations (CaseAlt' i) i where
  annotFtvMapM con ca0 = case ca0 of
    [caQ|' $x → $e |]           → afm con (x, e)
    [caQ|' $antiC:a |]          → $antifail

instance Id i ⇒ HasAnnotations (Binding' i) i where
  annotFtvMapM con bn0 = case bn0 of
    [bnQ|' $lid:_ = $e |]       → afm con  e
    [bnQ|' $antiB:a |]          → $antifail

