-- | Pretty-printing
{-# LANGUAGE
      PatternGuards,
      QuasiQuotes,
      TypeSynonymInstances,
      UnicodeSyntax
    #-}
module Syntax.Ppr (
  pprTyApp,
  -- * Re-exports
  module Syntax.PprClass,
  module Syntax.Prec
) where

import Meta.Quasi
import Syntax.PprClass
import Syntax.Prec
import AST
import Util

import qualified Syntax.Strings as Strings
import qualified AST.Decl
import qualified AST.Expr
import qualified AST.Notable
import qualified AST.Patt
import Data.Loc

import Prelude ()
import Data.List (sortBy)

instance IsInfix (Type i) where
  isInfix [ty| ($_, $_) $lid:n |] = isOperator n
  isInfix [ty| $_ -[$_]> $_ |]    = True
  isInfix _                        = False

-- | For printing infix expressions.  Given a splitter function that
--   splits expressions into a left operand, operator name, and right
--   operand (if possible), and an expression to print, pretty-prints
--   the expression, but only if there is one level of infix to be
--   done.
pprInfix :: Ppr a =>
            (a -> Maybe (a, String, Maybe a)) ->
            a -> Maybe Doc
pprInfix inspect x0
  | Just (x1, op, Nothing) <- inspect x0
  , precOp op == Right precBang
    = let rloop x'
            | Just (x1', op', Nothing) <- inspect x'
            , precOp op == Right precBang
            = first (op':) (rloop x1')
            | otherwise
            = ([], x')
          (ops, x) = first (op:) (rloop x1)
       in Just $
            fsep (mapTail (nest 2) $ map text ops)
            <> pprPrec precBang x
  | Just (_, op, Just _) <- inspect x0
  , isOperator (lid op :: Lid Raw)
  , p <- precOp op
  , p /= Right precBang
    = Just $
        prec (id|||id $ p) $
          fcat $ mapTail (nest 2) $ loop p mempty x0
  | otherwise
    = Nothing
  where
  loop p suf x
    | Just (x1, op, Just x2) <- inspect x
    , precOp op == p
    = case precOp op of
        Left _  -> loop p (oper op) x1 ++ [ppr1 x2 <> suf]
        Right _ -> ppr1 x1 <> oper op : loop p suf x2
  loop _ suf x = [ ppr x <> suf ]
  oper s = case s of
    '@':_ -> text s
    "\\/" -> text Strings.join
    ';':_ -> text s <> space
    _     -> space <> text s <> space

instance Ppr (Type i) where
  ppr [ty| $t1 -> $t2 |]
            = prec precArr $
              sep [ ppr1 t1, text Strings.uArrow <+> pprRight t2 ]
  ppr [ty| $t1 -[$q]> $t2 |]
            = prec precArr $
              sep [ ppr1 t1,
                    text Strings.arrowPre <> ppr0 q <>
                    text Strings.arrowPost <+> pprRight t2 ]
  ppr [ty| [ $t ] |]
                    = atPrec precStart $
                        pprVariantRow (lbrack <+>) t (<+> rbrack)
  ppr [ty| { $t } |] = pprRecordType t
  ppr [ty| $t ... |] = prec precApp $ sep [ ppr t, text Strings.ellipsis ]
  ppr t@[ty| ($list:ts) $qlid:n |]
    | Just doc <- pprInfix unfoldType t
                    = doc
    | null ts       = ppr n
    | otherwise     = prec precApp $ sep [ ppr ts, ppr n ]
  ppr [ty| '$x |]  = ppr x
  ppr [ty| $quant:qu '$x. $t |]
                    = prec precDot $
                        ppr qu <+>
                        fsep (map ppr1 tvs) <>
                        char '.'
                          >+> ppr body
      where (tvs, body) = unfoldTyQu qu [ty| $quant:qu '$x. $t |]
  ppr [ty| mu '$x. $t |]
                    = prec precDot $
                        text Strings.mu <+>
                        ppr1 x <>
                        char '.'
                          >+> ppr t
  ppr t@[ty| `$uid:_ of $_ | $_ |]
                       = pprVariantRow id t id
  ppr [ty| $anti:a |] = ppr a

unfoldType :: Type i -> Maybe (Type i, String, Maybe (Type i))
unfoldType [ty| ($t1, $t2) $name:n |] = Just (t1, n, Just t2)
unfoldType [ty| $t1 $name:n |]        = Just (t1, n, Nothing)
unfoldType _                           = Nothing

pprVariantRow ∷ (Doc → Doc) → Type i → (Doc → Doc) → Doc
pprVariantRow pre t post =
  case items' ++ end' of
    []   → pre (post mempty)
    docs → prec precStart .
           sep .
           mapHead pre .
           mapLast post .
           mapTail (char '|' <+>) $
             docs
  where
    (items, end) = unfoldTyRow t
    items' = [ char '`' <> ppr ni <+>
                 case ti of
                   [ty| unit |] → mempty
                   _ → text "of" <+> ppr1 ti
             | (ni, ti) ← sortBy (compare`on`show.fst) items ]
    end'   = case end of
      [ty| '$x |]     → [ppr1 x]
      [ty| $anti:a |] → [ppr1 a]
      _               → []

pprRecordType ∷ Type i → Doc
pprRecordType t = case items' ++ end' of
  []   → braces mempty
  docs → atPrec precStart .
         fsep .
         mapHead (lbrace <+>) .
         mapTail (nest 2) .
         mapLast (<+> rbrace) .
         mapInit (<> comma) $
           docs
  where
    (uitems, end) = unfoldTyRow t
    items         = first uidToLid <$> uitems
    items' = [ ppr ni <> colon <+> ppr1 ti
             | (ni, ti) ← sortBy (compare`on`show.fst) items ]
    end'   = case end of
      [ty| '$x |]     → [ppr1 x]
      [ty| $anti:a |] → [ppr1 a]
      _               → []

instance Ppr (TyPat i) where
  ppr tp0 = case tp0 of
    _ | Just doc <- pprInfix unfoldTyPat tp0
                       -> doc
    N _ (TpVar tv var) -> pprParamV var tv
    N _ (TpRow tv var) -> pprParamV var tv <+> text Strings.ellipsis
    [tpQ| [ $tp ] |]   -> lbrack <+> ppr0 tp <+> rbrack
    [tpQ| { $tp } |]   -> lbrace <+> ppr0 tp <+> rbrace
    [tpQ| $qlid:ql |]  -> ppr ql
    [tpQ| ($list:tps) $qlid:ql |]
                       -> prec precApp $ sep [ppr tps, ppr ql]
    [tpQ| $antiP:a |]  -> ppr a

unfoldTyPat :: TyPat i -> Maybe (TyPat i, String, Maybe (TyPat i))
unfoldTyPat [tpQ| ($t1, $t2) $name:n |] = Just (t1, n, Just t2)
unfoldTyPat [tpQ| $t1 $name:n |]        = Just (t1, n, Nothing)
unfoldTyPat _                           = Nothing

instance Ppr (QExp i) where
  ppr [qeQ| $qlit:qu |]   = ppr qu
  ppr [qeQ| $qvar:v |]    = ppr (tvname v)
  ppr [qeQ| $qe1, $qe2 |] = ppr qe1 <> comma <> ppr qe2
  ppr [qeQ| $anti:a |]    = ppr a

instance Ppr (Prog i) where
  ppr [prQ| $list:ms |]       = vcat (map ppr0 ms)
  ppr [prQ| $expr:e |]        = ppr e
  ppr [prQ| $list:ms in $e |] = vcat (map ppr0 ms) $+$
                                 (text "in" >+> ppr e)

instance Ppr (Decl i) where
  ppr [dc| let $lid:x = $e |] =
    prec precDot $
      pprLet (text "let" <+> ppr x) e False
  ppr [dc| let $x = $e |] =
    prec precDot $
      text "let" <+> ppr x <+> equals
        >+> ppr e
  ppr [dc| type $list:tds |] = pprTyDecs tds
  ppr [dc| abstype $list:ats0 with $list:ds end |] =
    case ats0 of
      []     ->
        vcat [
          text "abstype with",
          nest 2 $ vcat (map ppr ds),
          text "end"
        ]
      at:ats ->
        vcat [
          vcat (text "abstype" <+> pprAbsTy at :
                [ nest 4 $ text "and" <+> pprAbsTy ati | ati <- ats ])
            <+> text "with",
          nest 2 $ vcat (map ppr ds),
          text "end"
        ]
  ppr [dc| open $b |] = pprModExp (text "open" <+>) b
  ppr [dc| module $uid:n : $s = $b |] = pprModExp add1 b where
    add1 body = pprSigExp add2 s <+> equals <+> body
    add2 body = text "module" <+> ppr n <+> colon <+> body
  ppr [dc| module $uid:n = $b |] = pprModExp add b where
    add body = text "module" <+> ppr n <+> equals <+> body
  ppr [dc| module type $uid:n = $s |] = pprSigExp add s where
    add body = text "module type" <+> ppr n <+> equals <+> body
  ppr [dc| local $list:d0 with $list:d1 end |] =
    vcat [
      text "local",
      nest 2 (vcat (map ppr d0)),
      text "with",
      nest 2 (vcat (map ppr d1)),
      text "end"
    ]
  ppr [dc| exception $uid:n of $opt:mt |] =
    pprExcDec n mt
  ppr [dc| $anti:a |] = ppr a

pprTyDecs :: [TyDec i] -> Doc
pprTyDecs tds =
  vcat $
    mapHead (text "type" <+>) $
      mapTail ((nest 1) . (text "and" <+>)) $
        map ppr tds

pprExcDec :: Uid i -> Maybe (Type i) -> Doc
pprExcDec u Nothing  =
  text "exception" <+> ppr u
pprExcDec u (Just t) =
  text "exception" <+> ppr u <+> text "of" <+> ppr t

instance Ppr (TyDec i) where
  ppr td = case view td of
    TdAbs n ps vs gs qs -> pprProtoV n vs ps
                             >?> pprGuards gs
                             >?> pprQuals qs
    TdSyn n [(ps,t)]    -> pprProto n ps >+> equals <+> ppr t
    TdSyn n cs          -> vcat [ char '|' <+> each ci | ci <- cs ]
      where
        each (ps, rhs) = pprProto n ps
                           >+> equals <+> ppr rhs
    TdDat n ps alts     -> pprProtoV n (repeat Invariant) ps
                             >?> pprAlternatives alts
    TdAnti a            -> ppr a

pprAbsTy :: AbsTy i -> Doc
pprAbsTy at = case view at of
  AbsTy variances qual (N _ (TdDat name params alts)) ->
    pprProtoV name variances params
      >?> pprQuals qual
      >?> pprAlternatives alts
  AbsTy _ _ td -> ppr td -- shouldn't happen (yet)
  AbsTyAnti a -> ppr a

pprProto  :: Lid i -> [TyPat i] -> Doc
pprProto n ps = ppr (tpApp (J [] n) ps)

pprProtoV :: Lid i -> [Variance] -> [TyVar i] -> Doc
pprProtoV n vs tvs = pprProto n (zipWith tpVar tvs vs)

pprParamV :: Variance -> TyVar i -> Doc
pprParamV Invariant tv = ppr tv
pprParamV v         tv = ppr v <> ppr tv

pprGuards :: [TyVar i] -> Doc
pprGuards []  = mempty
pprGuards tvs = brackets $ text "rec" <+> fsep (ppr <$> tvs)

pprQuals :: QExp i -> Doc
pprQuals [qeQ| U |] = mempty
pprQuals qs          = text ":" <+> pprPrec precApp qs

pprAlternatives :: [(Uid i, Maybe (Type i))] -> Doc
pprAlternatives [] = equals
pprAlternatives (a:as) = sep $
  equals <+> alt a : [ char '|' <+> alt a' | a' <- as ]
  where
    alt (u, Nothing) = ppr u
    alt (u, Just t)  = ppr u <+> text "of" <+> pprPrec precDot t

pprModExp :: (Doc -> Doc) -> ModExp i -> Doc
pprModExp add modexp = case modexp of
  [me| $quid:n |] -> add (ppr n)
  [me| $quid:n $list:qls |] ->
    add (ppr n) <+>
    brackets (fsep (punctuate comma (map ppr qls)))
  [me| struct $list:ds end |] ->
    add (text "struct")
    $$ nest 2 (vcat (map ppr0 ds))
    $$ text "end"
  [me| $me1 : $se2 |] ->
    pprSigExp (pprModExp add me1 <+> colon <+>) se2
  [me| $anti:a |] -> add (ppr a)

pprSigExp :: (Doc -> Doc) -> SigExp i -> Doc
pprSigExp add se0 = body >+> withs where
  (wts, se1) = unfoldSeWith se0
  body       = case se1 of
    [seQ| $quid:n |] -> add (ppr n)
    [seQ| $quid:n $list:qls |] ->
      add (ppr n) <+>
      brackets (fsep (punctuate comma (map ppr qls)))
    [seQ| sig $list:sgs end |] ->
      add (text "sig")
      $$ nest 2 (vcat (map ppr0 sgs))
      $$ text "end"
    [seQ| $_ with type $list:_ $qlid:_ = $_ |] ->
      error "BUG! can't happen in pprSigExp"
    [seQ| $anti:a |] -> add (ppr a)
  withs      =
    atPrec 0 $ sep $
      mapHead (text "with type" <+>) $
        mapTail ((nest 6) . (text "and" <+>)) $
          [ pprTyApp tc tvs <+> equals <+> ppr t
          | (tc, tvs, t) <- wts ]

instance Ppr (SigItem i) where
  ppr sg0 = case sg0 of
    [sgQ| val $lid:n : $t |] ->
      text "val" <+> ppr n >+> colon <+> ppr t
    [sgQ| type $list:tds |] ->
      pprTyDecs tds
    [sgQ| module $uid:u : $s |] ->
      pprSigExp add s where
        add body = text "module" <+> ppr u <+> colon <+> body
    [sgQ| module type $uid:u = $s |] ->
      pprSigExp add s where
        add body = text "module type" <+> ppr u <+> equals <+> body
    [sgQ| include $s |] ->
      pprSigExp (text "include" <+>) s
    [sgQ| exception $uid:u of $opt:mt |] ->
      pprExcDec u mt
    [sgQ| $anti:a |] ->
      ppr a

instance Ppr (Expr i) where
  ppr e0 = case e0 of
    _ | Just doc <- pprInfix unfoldExpr e0
                       -> doc
    [ex| $qlid:x |]    -> ppr x
    [ex| $lit:lt |]    -> ppr lt
    [ex| $quid:x |]    -> ppr x
    [ex| $quid:x $e |] -> prec precApp (sep [ ppr x, ppr1 e ])
    [ex| `$uid:x |]    -> char '`' <> ppr x
    [ex| `$uid:x $e |] -> prec precApp (sep [ char '`' <> ppr x, ppr1 e ])
    [ex| #$uid:x $e |] -> prec precApp (sep [ char '#' <> ppr x, ppr1 e ])
    [ex| if $ec then $et else $ef |] ->
      prec precDot $
        sep [ text "if" <+> ppr ec,
              nest 2 $ text "then" <+> ppr0 et,
              nest 2 $ text "else" <+> ppr ef ]
    [ex| $_; $_ |] ->
      prec precExSemi $
        sep (unfold e0)
      where unfold [ex| $e1; $e2 |] = ppr1 e1 <> semi : unfold e2
            unfold e                 = [ ppr0 e ]
    [ex| let $lid:x = $e1 in $e2 |] ->
      prec precDot $
        hangLet (pprLet (text "let" <+> ppr x) e1 True) e2
    [ex| let $x = $e1 in $e2 |] ->
      prec precDot $
        hangLet (text "let" <+> ppr x <+> equals
                  >+> ppr e1 <+> text "in")
                e2
    [ex| match $e1 with $list:clauses |] ->
      prec precDot $
        vcat (sep [ text "match",
                    nest 2 $ ppr0 e1,
                    text "with" ] : map ppr clauses)
    [ex| let rec $list:bs in $e2 |] ->
      prec precDot $
        text "let" <+>
        vcat (zipWith pprBinding ("rec" : repeat "and") bs) $$
        nest 1 (text "in" <+> ppr e2)
    [ex| let $decl:d in $e2 |] ->
      prec precDot $
        hangLet
          (text "let" <+> ppr0 d <+> text "in")
          e2
    [ex| ($e1, $e2) |] ->
      prec precCom $
        sep [ ppr e1 <> comma, ppr1 e2 ]
    [ex| λ $_ → $_ |]  ->
      prec precDot $
        hang
          (text Strings.fun <+>
           fsep (pprPrec1 precApp <$> args) <+>
           text Strings.arrow)
          2
          (ppr body)
        where (args, body) = unfoldExAbs e0
    [ex| $e1 $e2 |]
          -> prec precApp $
               sep [ ppr e1, ppr1 e2 ]
    [ex| ( $e : $t1 :> $t2 ) |] ->
      prec precCast $
        atPrec (precCast + 2) $
          sep [ ppr e,
                colon     <+> ppr t1,
                text ":>" <+> ppr t2 ]
    [ex| ( $e : $t1 ) |] ->
      prec precCast $
        atPrec (precCast + 2) $
          sep [ ppr e,
                colon <+> ppr t1 ]
    [ex| ( $e :> $t1 ) |] ->
      prec precCast $
        atPrec (precCast + 2) $
          sep [ ppr e,
                text ":>" <+> ppr t1 ]
    [ex| $anti:a |] -> ppr a
    where
    unfoldExpr [ex| ($name:x $e1) $e2 |] = Just (e1, x, Just e2)
    unfoldExpr [ex| $name:x $e1 |]       = Just (e1, x, Nothing)
    unfoldExpr _                          = Nothing

pprBinding :: String -> Binding i -> Doc
pprBinding kw [bnQ| $lid:x = $e |] = pprLet (text kw <+> ppr x) e True
pprBinding kw [bnQ| $antiB:a |]    = text kw <+> ppr a

instance Ppr (CaseAlt i) where
  ppr [caQ| $xi -> $ei |] =
    hang (char '|' <+> ppr xi <+> text Strings.arrow)
         4
         (ppr ei)
  ppr [caQ| $antiC:a |]   = char '|' <+> ppr a

-- | Print a let expression, indenting the body only if the body is
--   not another let expression.
hangLet ∷ Doc → Expr i → Doc
hangLet doc e2 = hang doc (if (isLet e2) then 0 else 2) (ppr e2)
  where
  isLet [ex| $_; $_ |]                = False
  isLet [ex| let $_ = $_ in $_ |]     = True
  isLet [ex| let rec $list:_ in $_ |] = True
  isLet _                             = False

-- | Print the binding and rhs of a let
pprLet :: Doc -> Expr i -> Bool -> Doc
pprLet doc e1 withIn =
  doc <+>
  nest 2 (fsep (pprPrec1 precApp <$> args)) <+>
  maybe mempty (nest 2 . (colon <+>) . ppr0) mannot <+> equals
    >+> ppr rhs <+> if withIn then text "in" else mempty
  where
    (args, rhs, mannot) = resugarLet e1

-- | Given the rhs of a let expression, pull out the arguments and
--   any result-type annotation.
resugarLet ∷ Expr i → ([Patt i], Expr i, Maybe (Type i))
resugarLet e =
  let (args, rhs0)  = unfoldExAbs e
   in case rhs0 of
        [ex| $e' : $t |] → (args, e', Just t)
        _                → (args, rhs0, Nothing)

instance Ppr (Patt i) where
  ppr [pa| _ |]             = text "_"
  ppr [pa| $lid:l |]        = ppr l
  ppr [pa| $quid:qu |]      = ppr qu
  ppr [pa| $quid:qu $x |]   = prec precApp $
                                 ppr qu <+> ppr1 x
  ppr [pa| ($x, $y) |]      = prec precCom $
                                 ppr x <> comma <+> ppr1 y
  ppr [pa| $lit:lt |]       = ppr lt
  ppr [pa| $x as $lid:l |]  = prec precDot $
                                 ppr1 x <+> text "as" <+> ppr l
  ppr [pa| `$uid:u |]       = char '`' <> ppr u
  ppr [pa| `$uid:u $x |]    = prec precApp $
                                char '`' <> ppr u <+> ppr1 x
  ppr [pa| ! $x |]          = prec precBang $
                                char '!' <> ppr1 x
  ppr [pa| $x : $t |]       = prec precCast $
                                hang (ppr x)
                                     2
                                     (colon <+> ppr0 t)
  ppr [pa| $anti:a |]       = ppr a

instance Ppr Lit where
  ppr (LtInt i)   = integer i
  ppr (LtChar c)  = text (show c)
  ppr (LtFloat f) = double f
  ppr (LtStr s)   = text (show s)
  ppr (LtAnti a)  = ppr a

--
-- Helper for pretty-printing type-like things -- doesn't require
-- underlying types, but does need to see the operator name.
--

data PprTyAppHelper i a
  = PTAHBranch (QLid i) [a]
  | PTAHLeaf   a

instance Ppr a => Ppr (PprTyAppHelper i a) where
  ppr (PTAHLeaf a) = ppr a
  ppr _            = error "BUG! in PprTyAppHelper.ppr"

unfoldPTAH :: PprTyAppHelper i a ->
              Maybe (PprTyAppHelper i a, String, Maybe (PprTyAppHelper i a))
unfoldPTAH (PTAHBranch (J [] l) [a, b])
  = Just (PTAHLeaf a, unLid l, Just (PTAHLeaf b))
unfoldPTAH (PTAHBranch (J [] l) [a])
  = Just (PTAHLeaf a, unLid l, Nothing)
unfoldPTAH _
  = Nothing

pprTyApp :: Ppr a => QLid i -> [a] -> Doc
pprTyApp ql ts
  | Just doc <- pprInfix unfoldPTAH (PTAHBranch ql ts)
               = doc
pprTyApp ql [] = ppr ql
pprTyApp ql ts = prec precApp $ sep [ ppr ts, ppr ql ]

--
-- Instances
--

instance Show (Prog i)   where showsPrec = showFromPpr
instance Show (Decl i)   where showsPrec = showFromPpr
instance Show (TyDec i)  where showsPrec = showFromPpr
instance Show (Expr i)   where showsPrec = showFromPpr
instance Show (Patt i)   where showsPrec = showFromPpr
instance Show Lit        where showsPrec = showFromPpr
instance Show (Type i)   where showsPrec = showFromPpr
instance Show (TyPat i)  where showsPrec = showFromPpr
instance Show (QExp i)   where showsPrec = showFromPpr
instance Show (SigItem i)where showsPrec = showFromPpr

instance Ppr Loc       where pprPrec = pprFromShow
instance Ppr QLit      where pprPrec = pprFromShow
instance Ppr Variance  where pprPrec = pprFromShow
instance Ppr Quant     where pprPrec = pprFromShow
instance Ppr (Lid i)   where pprPrec = pprFromShow
instance Ppr (Uid i)   where pprPrec = pprFromShow
instance Ppr (BIdent i)where pprPrec = pprFromShow
instance Ppr (TyVar i) where pprPrec = pprFromShow
instance Ppr Anti      where pprPrec = pprFromShow
instance (Show p, Show k) => Ppr (Path p k) where pprPrec = pprFromShow

