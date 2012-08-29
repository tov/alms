-- | Utilities for constructing syntax
module Syntax.Construction (
  -- * Generic tuple building
  ToTuple(..),
  -- * Optimizing expression constructors
  exLet', exLetVar', exAbs', exAbsVar',
  -- * Substitution
  substExpr,
) where

import Util
import AST
import Data.Loc
import Meta.Quasi

import Prelude ()
import Data.Map as M hiding (foldr, foldl')
import Data.Generics (Data, everywhere, mkT)

-- | Constructs a let expression, but with a special case:
--
--   @let x      = e in x        ==   e@
--   @let (x, y) = e in (x, y)   ==   e@
--   @let x      = v in e        ==   [v/x]e@
--
-- This is always safe to do.
exLet' :: Tag i => Patt i -> Expr i -> Expr i -> Expr i
exLet' π e1 e2
  | π -==+ e2           = e1
  -- This case can cause code bloat:
  | [pa| $vid:x |] ← π
  , syntacticValue e1   = substExpr e1 (J [] x) e2
  | [pa| $vid:x |] ← π
  , qx ← J [] x
  , nextRedex qx e2
  , M.lookup qx (fv e2) == Just 1
                        = substExpr e1 (J [] x) e2
  | otherwise           = exLet π e1 e2

-- | Constructs a let expression whose pattern is a variable.
exLetVar' :: Tag i => VarId i -> Expr i -> Expr i -> Expr i
exLetVar'  = exLet' . paVar

-- | Constructs a lambda expression, but with a special case:
--
--    @exAbs' x     (exApp (exVar f) x)      ==  exVar f@
--    @exAbs' (x,y) (exApp (exVar f) (x,y))  ==  exVar f@
--
-- This eta-contraction is always safe, because f has no effect
exAbs' :: Tag i => Patt i -> Expr i -> Expr i
exAbs' x e = case view e of
  ExApp e1 e2 -> case view e1 of
    ExVar (J p f) | x -==+ e2
              -> exVar (J p f)
    _         -> exAbs x e
  _           -> exAbs x e

-- | Construct an abstraction whose pattern is just a variable.
exAbsVar' :: Tag i => VarId i -> Expr i -> Expr i
exAbsVar'  = exAbs' . paVar

-- | Does a pattern exactly match an expression?  That is, is
--   @let p = e1 in e@ equivalent to @e1@?  Note that we cannot
--   safely handle data constructors, because they may fail to match.
(-==+) :: Tag i => Patt i -> Expr i -> Bool
p -==+ e = case (dataOf p, dataOf e) of
  (PaVar l,      ExVar (J [] l'))
    -> l == l'
  (PaCon (J [] (ConId (Uid _ "()"))) Nothing,
   ExCon (J [] (ConId (Uid _ "()"))) Nothing)
    -> True
  (PaPair p1 p2, ExPair e1 e2)
    -> p1 -==+ e1 && p2 -==+ e2
  _ -> False
infix 4 -==+

-- Does the given variable appear where the next redex would be
-- for the expression, if a substitution were made? This, along with
-- linearity (a separate check) makes it safe to substitute any expression
-- for it.
nextRedex ∷ Tag i ⇒ QVarId i → Expr i → Bool
nextRedex x = loop where
  e1 >*> b2 = loop e1
           || syntacticValue e1
              && x `M.notMember` fv e1
              && b2
  loop e = case e of
    [ex| $qvid:x' |]            → x == x'
    [ex| $lit:_ |]              → False
    [ex| $qcid:_ $opt:me |]     → maybe False loop me
    [ex| let $vid:x' = $e1 in $e2 |]
      | J [] x' == x            → loop e1
      | otherwise               → e1 >*> loop e2
    [ex| let $_ = $e1 in $_ |]  → loop e1
    [ex| match $e0 with $list:_ |]
                                → loop e0
    [ex| let rec $list:bns in $e2 |]
                                → x `M.notMember` fv bns
                               && x ∉ qdv bns
                               && loop e2
    [ex| let $decl:_ in $_ |]   → False
    [ex| ($e1, $e2) |]          → e1 >*> loop e2
    [ex| λ $_ → $_ |]           → False
    [ex| $e1 $e2 |]             → e1 >*> loop e2
    [ex| `$uid:_ $opt:me2 |]    → maybe False loop me2
    [ex| #$uid:_ $e2 |]         → loop e2
    [ex| { $list:flds | $e2 } |]
                                → foldr (>*>) (loop e2)
                                        (fdexpr . view <$> flds)
    [ex| {+ $list:_ | $e2 +} |] → loop e2
    [ex| $e1.$uid:_ |]          → loop e1
    [ex| $e1 : $_ |]            → loop e1
    [ex| $e1 :> $_ |]           → loop e1
    [ex| $anti:a |]             → $antierror

-- Substitute an expression for a variable
substExpr ∷ Tag i ⇒ Expr i → QVarId i → Expr i → Expr i
substExpr e' x' = loop where
  fv_e'  = [ x | J [] x ← M.keys (fv e') ]
  loop e = case e of
    [ex| $qvid:x |]
      | x == x'                 → e'
      | otherwise               → e
    [ex| $lit:_ |]              → e
    [ex| $qcid:c $opt:me |]     → [ex| $qcid:c $opt:me' |]
      where me' = loop <$> me
    [ex| let $π = $e1 in $e2 |]
      | x' ∈ qdv π              → [ex| let $π = $e1' in $e2 |]
      | otherwise               → [ex| let $π' = $e1' in $e2' |]
      where e1'        = loop e1
            (π', e2'0) = avoidCapture fv_e' x' π e2
            e2'        = loop e2'0
    [ex| match $e0 with $list:cas |]
                                → [ex| match $e0' with $list:cas' |]
      where e0'  = loop e0
            cas' = substCaseAlt e' x' <$> cas
    [ex| let rec $list:bns in $e2 |]
      | x' ∈ (J [] <$> fs)      → [ex| let rec $list:bns' in $e2 |]
      where fs   = [ fi | [bnQ|! $vid:fi = $_ |] ← bns ]
            bns' = substBinding e' x' <$> bns
    [ex| let rec $list:bns in $e2 |]
      | otherwise               → [ex| let rec $list:bns' in $e2' |]
      where
      (fs, es)       = unzip [ (fi, ei) | [bnQ|! $vid:fi = $ei |] ← bns ]
      (fs', renamer) = avoidCapture' fv_e' x' fs (e2:es)
      bns'           = reverse (fst (foldl' eachBn ([], fs') bns))
      e2'            = loop (renamer e2)
      eachBn (acc, fi':rest) [bnQ| $vid:_ = $ei |]
                     = ([bnQ| $vid:fi' = $ei' |]:acc, rest)
                       where ei' = loop (renamer ei)
      eachBn (acc, rest)     bn@[bnQ| $antiB:_ |]
                     = (bn:acc, rest)
      eachBn _ _     =
        error "BUG in substExpr: Inconsistency in number of let rec bindings"
    [ex| let $decl:d in $e2 |]  → [ex| let $decl:d in $e2' |]
      where e2' = loop e2        -- Doesn't handle d
    [ex| ($e1, $e2) |]          → [ex| ($e1', $e2') |]
      where e1' = loop e1
            e2' = loop e2
    [ex| λ $π1 → $e2 |]
      | x' ∈ qdv π1             → e
      | otherwise               → [ex| λ $π1' → $e2' |]
      where (π1', e2')  = second loop
                        $ avoidCapture fv_e' x' π1 e2
    [ex| $e1 $e2 |]             → [ex| $e1' $e2' |]
      where e1' = loop e1
            e2' = loop e2
    [ex| `$uid:c $opt:me2 |]    → [ex| `$uid:c $opt:me2' |]
      where me2' = loop <$> me2
    [ex| #$uid:c $e2 |]         → [ex| #$uid:c $e2' |]
      where e2' = loop e2
    [ex| { $list:flds | $e2 } |]
                                → [ex| { $list:flds' | $e2' } |]
      where flds' = substField e' x' <$> flds
            e2'   = loop e2
    [ex| {+ $list:flds | $e2 +} |]
                                → [ex| {+ $list:flds' | $e2' +} |]
      where flds' = substField e' x' <$> flds
            e2'   = loop e2
    [ex| $e1.$uid:u |]          → [ex| $e1'.$uid:u |]
      where e1' = loop e1
    [ex| $e1 : $annot |]        → [ex| $e1' : $annot |]
      where e1' = loop e1
    [ex| $e1 :> $annot |]       → [ex| $e1' : $annot |]
      where e1' = loop e1
    [ex| $anti:_ |]             → e

substCaseAlt ∷ Tag i ⇒ Expr i → QVarId i → CaseAlt i → CaseAlt i
substCaseAlt e' x' ca = case ca of
  [caQ| $π1 → $e2 |]
    | x' ∈ qdv π1               → ca
    | otherwise                 → [caQ| $π1' → $e2' |]
      where (π1', e2') = second (substExpr e' x')
                       $ avoidCapture [ x | J [] x ← M.keys (fv e') ]
                                      x' π1 e2
  [caQ| #$uid:c → $e2 |]        → [caQ| #$uid:c → $e2' |]
      where e2'         = substExpr e' x' e2
  [caQ| #$uid:c $π1 → $e2 |]
    | x' ∈ qdv π1               → ca
    | otherwise                 → [caQ| #$uid:c $π1' → $e2' |]
      where (π1', e2') = second (substExpr e' x')
                       $ avoidCapture [ x | J [] x ← M.keys (fv e') ]
                                      x' π1 e2
  [caQ| $antiC:_ |]             → ca

substBinding ∷ Tag i ⇒ Expr i → QVarId i → Binding i → Binding i
substBinding e' x' bn = case bn of
  [bnQ| $vid:f = $e2 |]
    | x' == J [] f              → bn
    | otherwise                 → [bnQ| $vid:f' = $e2' |]
      where
      (f', e2') = second (substExpr e' x')
                $ avoidCapture [ x | J [] x ← M.keys (fv e') ]
                               x' f e2
  [bnQ| $antiB:_ |]             → bn

substField ∷ Tag i ⇒ Expr i → QVarId i → Field i → Field i
substField e' x' fld = case fld of
  [fdQ| $uid:u = $e2 |] → [fdQ| $uid:u = $e2' |]
    where e2' = substExpr e' x' e2
  [fdQ| $antiF:_ |]     → fld

-- | Given a list of names not to capture, the variable being
--  substituted, a pattern, and an expression
-- in the scope of the pattern, rename the pattern and expression
-- together so that it's safe to substitute the names under the pattern.
avoidCapture ∷ (Data a, Dv a i, Tag i) ⇒
               [VarId i] → QVarId i → a → Expr i → (a, Expr i)
avoidCapture fv_e' x' π e = second ($ e) (avoidCapture' fv_e' x' π e)

-- | Given a list of names not to capture, the variable being
-- substituted, a pattern, and an expression
-- in the scope of the pattern, rename the pattern and expression
-- together so that it's safe to substitute the names under the pattern.
avoidCapture' ∷ (Data a, Dv a i, Fv b i, Tag i) ⇒
                [VarId i] → QVarId i → a → b → (a, Expr i → Expr i)
avoidCapture' fv_e' x' π e
  | x' ∈ qdv π || x' `M.notMember` fv e = (π, id)
  | otherwise                           = (π', r)
  where
    fv_e  = [ idName x | J [] x ← M.keys (fv e) ]
    vs    = dv π ∩ fv_e'
    vs'   = ident <$> freshNames (Just . idName <$> vs)
                                 (fv_e ++ (idName <$> fv_e')) []
    π'    = foldr2 (\v v' → renameGeneric v' v) π vs vs'
    r e'  = foldr2 (\v v' → substExpr (exBVar v') (J [] v)) e' vs vs'

-- | Rename a variable
renameGeneric ∷ (Tag i, Data a) ⇒ VarId i → VarId i → a → a
renameGeneric x' x = everywhere (mkT each) where
  each y | x == y = x'
  each a          = a

---
--- GENERIC TUPLING
---

class ToTuple a b c where
  (-*-) ∷ a → [b] → c

infixl 3 -*-

instance (Tag i, ToPatt a i, ToPatt b i) ⇒ ToTuple a b (Patt i) where
  π -*- πs = foldl' paPair (toPatt π) (toPatt <$> πs)

instance (Tag i, ToExpr a i, ToExpr b i) ⇒ ToTuple a b (Expr i) where
  π -*- πs = foldl' exPair (toExpr π) (toExpr <$> πs)
