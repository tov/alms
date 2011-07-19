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
import Meta.Quasi

import Prelude ()
import qualified Data.Map as M
import qualified Data.Set as S

-- | A type annotation is merely a syntactic type
type Annot i = Type i

-- | Find out the free variables of a type annotation.  Minimal
--   definition: @annotFtvMap@
class Tag i ⇒ HasAnnotations a i | a → i where
  -- | Accumulate information about type variables.
  annotFtvMap   ∷ (TyVar i → r) →
                  (QTypId i → Int → r → r) →
                  (r → r → r) →
                  a →
                  M.Map (TyVar i) r
  -- | Just the set of type variables, please.
  annotFtvSet   ∷ a → S.Set (TyVar i)
  annotFtvSet   = M.keysSet . annotFtvMap (\_ → ()) (\_ _ () → ()) (\_ _ → ())

-- | Shorter-named alias
afm ∷ HasAnnotations a i ⇒
      (TyVar i → r) →
      (QTypId i → Int → r → r) →
      (r → r → r) →
      a →
      M.Map (TyVar i) r
afm = annotFtvMap

--
-- Generic instances
--

instance (HasAnnotations a i, HasAnnotations b i) ⇒
         HasAnnotations (a, b) i where
  annotFtvMap var con cmb (a, b) =
    M.unionWith cmb (afm var con cmb a) (afm var con cmb b)

instance (HasAnnotations a i, HasAnnotations b i, HasAnnotations c i) ⇒
         HasAnnotations (a, b, c) i where
  annotFtvMap var con cmb (a, b, c) = afm var con cmb (a, (b, c))

instance HasAnnotations a i ⇒ HasAnnotations [a] i where
  annotFtvMap var con cmb = M.unionsWith cmb . map (afm var con cmb)

instance HasAnnotations a i ⇒ HasAnnotations (Maybe a) i where
  annotFtvMap var con cmb = maybe mempty (afm var con cmb)

instance HasAnnotations a i ⇒ HasAnnotations (N note a) i where
  annotFtvMap = afm <$$$.> dataOf

--
-- Specific instances for syntax.
--

instance Tag i ⇒ HasAnnotations (TyVar i) i where
  annotFtvMap _   _ _ (TVAnti a) = $antierror
  annotFtvMap var _ _ tv         = M.singleton tv (var tv)

instance Tag i ⇒ HasAnnotations (QExp' i) i where
  annotFtvMap var con cmb qe0 = case qe0 of
    [qeQ|' $qlit:_   |]           → mempty
    [qeQ|'  '$tv |]               → afm var con cmb tv
    [qeQ|' $qe1 ⋁ $qe2 |]         → afm var con cmb (qe1, qe2)
    [qeQ|' $anti:a |]             → $antierror

instance Tag i ⇒ HasAnnotations (Type' i) i where
  annotFtvMap var con cmb t0 = case t0 of
    [ty|' ($list:ts) $qtid:ql |]  →
      M.unionsWith cmb
        [ con ql ix <$> afm var con cmb t
        | t  ← ts
        | ix ← [ 0 .. ] ]
    [ty|'  '$tv |]                → afm var con cmb tv
    [ty|' $t1 -[$opt:qe]> $t2 |]  →
      let t1m = con (qident "->") 0 <$> afm var con cmb t1
          qem = con (qident "->") 1 <$> afm var con cmb qe
          t2m = con (qident "->") 2 <$> afm var con cmb t2
       in M.unionsWith cmb [t1m, qem, t2m]
    [ty|' $quant:_ `$tv. $t |]    → M.delete tv $ afm var con cmb t
    [ty|' μ `$tv. $t |]           → M.delete tv $ afm var con cmb t
    [ty|' `$uid:_ of $t1 | $t2 |] → afm var con cmb (t1, t2)
    [ty|' $anti:a |]              → $antierror

instance Tag i => HasAnnotations (Patt' i) i where
  annotFtvMap var con cmb x0 = case x0 of
    [pa|' _ |]                  → mempty
    [pa|' $lid:_ |]             → mempty
    [pa|' $qcid:_ $opt:mx |]    → afm var con cmb mx
    [pa|' ($x, $y) |]           → afm var con cmb (x, y)
    [pa|' $lit:_ |]             → mempty
    [pa|' $x as $vid:_ |]       → afm var con cmb x
    [pa|' `$uid:_ $opt:mx |]    → afm var con cmb mx
    [pa|' $x : $t |]            → afm var con cmb (x, t)
    [pa|' ! $x |]               → afm var con cmb x
    [pa|' $anti:a |]            → $antierror

instance Tag i ⇒ HasAnnotations (Expr' i) i where
  annotFtvMap var con cmb e0 = case e0 of
    [ex|' $qvid:_ |]            → mempty
    [ex|' $lit:_ |]             → mempty
    [ex|' $qcid:_ $opt:me |]    → afm var con cmb me
    [ex|' let $x = $e in $e' |] → afm var con cmb (x, e, e')
    [ex|' match $e with $list:cas |]
                                → afm var con cmb (e, cas)
    [ex|' let rec $list:bns in $e |]
                                → afm var con cmb (bns, e)
    [ex|' let $decl:_ in $e |]  → afm var con cmb e
    [ex|' ($e1, $e2) |]         → afm var con cmb (e1, e2)
    [ex|' λ $x → $e |]          → afm var con cmb (x, e)
    [ex|' $e1 $e2 |]            → afm var con cmb (e1, e2)
    [ex|' `$uid:_ $opt:me |]    → afm var con cmb me
    [ex|' #$uid:_ $e |]         → afm var con cmb e
    [ex|' $e : $t |]            → afm var con cmb (e, t)
    [ex|' $e :> $t |]           → afm var con cmb (e, t)
    [ex|' $anti:a |]            → $antierror

instance Tag i ⇒ HasAnnotations (CaseAlt' i) i where
  annotFtvMap var con cmb ca0 = case ca0 of
    [caQ|' $x → $e |]           → afm var con cmb (x, e)
    [caQ|' $antiC:a |]          → $antierror

instance Tag i ⇒ HasAnnotations (Binding' i) i where
  annotFtvMap var con cmb bn0 = case bn0 of
    [bnQ|' $lid:_ = $e |]       → afm var con cmb  e
    [bnQ|' $antiB:a |]          → $antierror
