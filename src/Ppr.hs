-- | Pretty-printing
{-# LANGUAGE
      PatternGuards,
      QuasiQuotes,
      TypeSynonymInstances
    #-}
module Ppr (
  -- * Pretty-printing class
  Ppr(..),
  -- * Pretty-printing combinators
  parensIf, (>+>), (>?>), pprTyApp,
  -- * Renderers
  render, renderS, printDoc, printPpr,
  -- ** Instance helpers
  showFromPpr, pprFromShow,
  -- * Re-exports
  module Text.PrettyPrint,
  module Prec
) where

import Meta.Quasi
import Prec
import Syntax
import Util

import qualified Syntax.Decl
import qualified Syntax.Expr
import qualified Syntax.Notable
import qualified Syntax.Patt
import qualified Loc

import Text.PrettyPrint hiding (render)
import Data.List (intersperse)

-- | Class for pretty-printing at different types
--
-- Minimal complete definition is one of:
--
-- * 'pprPrec'
--
-- * 'ppr'
class Ppr p where
  -- | Print at the specified enclosing precedence
  pprPrec :: Int -> p -> Doc
  -- | Print at top-level precedence
  ppr     :: p -> Doc
  -- | Print a list at the specified enclosing precedence with
  --   the specified style
  pprPrecStyleList :: Int -> ListStyle -> [p] -> Doc
  -- | Print a list at the specified enclosing precedence
  pprPrecList :: Int -> [p] -> Doc
  -- | Print a list at top-level precedence
  pprList     :: [p] -> Doc
  -- | Style for printing lists
  listStyle   :: [p] -> ListStyle
  --
  ppr         = pprPrec precDot
  pprPrec _   = ppr
  pprPrecStyleList _ st [] =
    if listStyleDelimitEmpty st
      then listStyleBegin st <> listStyleEnd st
      else empty
  pprPrecStyleList p st [x] =
    if listStyleDelimitSingleton st
      then listStyleBegin st <> ppr x <> listStyleEnd st
      else pprPrec p x
  pprPrecStyleList _ st xs  =
    listStyleBegin st <>
      listStyleJoiner st (punctuate (listStylePunct st) (map ppr xs))
    <> listStyleEnd st
  pprPrecList p xs = pprPrecStyleList p (listStyle xs) xs
  pprList          = pprPrecList 0
  listStyle _ = ListStyle {
    listStyleBegin            = lparen,
    listStyleEnd              = rparen,
    listStylePunct            = comma,
    listStyleDelimitEmpty     = False,
    listStyleDelimitSingleton = False,
    listStyleJoiner           = fsep
  }

data ListStyle = ListStyle {
  listStyleBegin, listStyleEnd, listStylePunct :: Doc,
  listStyleDelimitEmpty, listStyleDelimitSingleton :: Bool,
  listStyleJoiner :: [Doc] -> Doc
}

-- | Conditionally add parens around the given 'Doc'
parensIf :: Bool -> Doc -> Doc
parensIf True  doc = parens doc
parensIf False doc = doc

instance Ppr a => Ppr [a] where
  pprPrec = pprPrecList

instance Ppr a => Ppr (Maybe a) where
  pprPrec _ Nothing  = empty
  pprPrec p (Just a) = pprPrec p a

class Ppr a => IsInfix a where
  isInfix  :: a -> Bool
  pprRight :: Int -> a -> Doc
  pprRight p a =
    if isInfix a
      then pprPrec p a
      else ppr a

instance Ppr Doc where
  ppr = id

instance IsInfix (Type i) where
  isInfix [$ty| ($_, $_) $lid:n |] = isOperator n
  isInfix [$ty| $_ -[$_]> $_ |]    = True
  isInfix _                        = False

-- | To pretty print the application of a type constructor to
--   generic parameters
pprTyApp :: (Ppr a) => Int -> QLid i -> [a] -> Doc
pprTyApp _ ql       []   = ppr ql
pprTyApp p (J [] l) [t1]
  | isOperator l, precOp (unLid l) == Right precBang
    = parensIf (p > precBang) $
        text (unLid l) <> pprPrec (precBang + 1) t1
pprTyApp p (J [] l) [t1, t2]
  -- print @ without space around it:
  | isOperator l, '@':_ <- unLid l, Right prec <- precOp (unLid l)
    = parensIf (p > prec) $
        pprPrec (prec + 1) t1 <> text (unLid l) <> pprPrec prec t2
  | isOperator l, Left prec <- precOp (unLid l)
    = parensIf (p > prec) $
        sep [ pprPrec prec t1,
              text (unLid l) <+> pprPrec (prec + 1) t2 ]
  | isOperator l, Right prec <- precOp (unLid l)
    = parensIf (p > prec) $
        sep [ pprPrec (prec + 1) t1,
              text (unLid l) <+> pprPrec prec t2]
pprTyApp p ql ts = parensIf (p > precApp) $
                     sep [ pprPrec precApp ts,
                           ppr ql ]

instance Ppr (Type i) where
  -- Print sugar for infix type constructors:
  pprPrec p [$ty| $t1 ; $t2 |]
                  = parensIf (p > precSemi) $
                      sep [ pprPrec (precSemi + 1) t1 <> text ";",
                            pprPrec precSemi t2 ]
  -- pprPrec p (TyFun q t1 t2)
  pprPrec p [$ty| $t1 -[$q]> $t2 |]
                  = parensIf (p > precArr) $
                    sep [ pprPrec (precArr + 1) t1,
                          pprArr (view q) <+> pprRight precArr t2 ]
    where pprArr (QeLit Qu) = text "->"
          pprArr (QeLit Qa) = text "-o"
          pprArr _          = text "-[" <> pprPrec precStart q <> text "]>"
  pprPrec p [$ty| ($list:ts) $qlid:n |]
                          = pprTyApp p n ts
    -- debugging: <> text (show (ttId (unsafeCoerce tag :: TyTag)))
  pprPrec p [$ty| '$x |]  = pprPrec p x
  pprPrec p [$ty| $quant:qu '$x. $t |]
                          = parensIf (p > precDot) $
                              ppr qu <+>
                              fsep (map (pprPrec (precDot + 1))
                                        tvs) <>
                              char '.'
                                >+> pprPrec precDot body
      where (tvs, body) = unfoldTyQu qu [$ty| $quant:qu '$x. $t |]
  pprPrec p [$ty| mu '$x. $t |]
                          = parensIf (p > precDot) $
                              text "mu" <+>
                              pprPrec (precDot + 1) x <>
                              char '.'
                                >+> pprPrec precDot t
  pprPrec p [$ty| $anti:a |] = pprPrec p a

instance Ppr (TyPat i) where
  pprPrec p tp0 = case tp0 of
    N _ (TpVar tv var) -> pprParamV var tv
    [$tpQ| ($list:tps) $qlid:ql |]
                       -> pprTyApp p ql tps
    [$tpQ| $antiP:a |] -> ppr a

instance Ppr (QExp i) where
  pprPrec p [$qeQ| $qlit:qu |] = pprPrec p qu
  pprPrec p [$qeQ| $qvar:v |]  = pprPrec p (tvname v)
  pprPrec p [$qeQ| $qdisj:qes |] = case qes of
    []    -> pprPrec p Qu
    [qe]  -> pprPrec p qe
    _     -> parensIf (p > precPlus) $
               fsep $
                 intersperse (text "\\/") $
                   map (pprPrec (precPlus + 1)) qes
  pprPrec p [$qeQ| $qconj:qes |] = case qes of
    []    -> pprPrec p Qa
    [qe]  -> pprPrec p qe
    _     -> parensIf (p > precStar) $
               hcat $
                 intersperse (text "/\\") $
                   map (pprPrec (precStar + 1)) qes
  pprPrec p [$qeQ| $anti:a |] = pprPrec p a

instance Ppr Int where
  ppr = int

instance Ppr (Prog i) where
  ppr [$prQ| $list:ms |]       = vcat (map ppr ms)
  ppr [$prQ| $expr:e |]        = ppr e
  ppr [$prQ| $list:ms in $e |] = vcat (map ppr ms) $+$
                                 (text "in" >+> ppr e)

instance Ppr (Decl i) where
  ppr [$dc| let $x = $e |] = sep
    [ text "let" <+> ppr x,
      nest 2 $ equals <+> ppr e ]
  ppr [$dc| let $x : $t = $e |] = sep
    [ text "let" <+> ppr x,
      nest 2 $ colon <+> ppr t,
      nest 4 $ equals <+> ppr e ]
  ppr [$dc| type $list:tds |] = pprTyDecs tds
  ppr [$dc| abstype $list:ats0 with $list:ds end |] =
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
  ppr [$dc| open $b |] = pprModExp (text "open" <+>) b
  ppr [$dc| module $uid:n : $s = $b |] = pprModExp add1 b where
    add1 body = pprSigExp add2 s <+> equals <+> body
    add2 body = text "module" <+> ppr n <+> colon <+> body
  ppr [$dc| module $uid:n = $b |] = pprModExp add b where
    add body = text "module" <+> ppr n <+> equals <+> body
  ppr [$dc| module type $uid:n = $s |] = pprSigExp add s where
    add body = text "module type" <+> ppr n <+> equals <+> body
  ppr [$dc| local $list:d0 with $list:d1 end |] =
    vcat [
      text "local",
      nest 2 (vcat (map ppr d0)),
      text "with",
      nest 2 (vcat (map ppr d1)),
      text "end"
    ]
  ppr [$dc| exception $uid:n of $opt:mt |] =
    pprExcDec n mt
  ppr [$dc| $anti:a |] = ppr a

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
    TdAbs n ps vs qs  -> pprProtoV n vs ps >?> pprQuals qs
    TdSyn n [(ps,t)]  -> pprProto n ps >+> equals <+> ppr t
    TdSyn n cs        -> vcat [ char '|' <+> each ci | ci <- cs ]
      where
        each (ps, rhs) = pprProto n ps
                           >+> char '=' <+> ppr rhs
    TdDat n ps alts   -> pprProtoV n (repeat Invariant) ps
                           >?> pprAlternatives alts
    TdAnti a          -> ppr a

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

pprQuals :: QExp i -> Doc
pprQuals [$qeQ| U |] = empty
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
  [$me| $quid:n |] -> add (ppr n)
  [$me| $quid:n $list:qls |] ->
    add (ppr n) <+>
    brackets (fsep (punctuate comma (map ppr qls)))
  [$me| struct $list:ds end |] ->
    add (text "struct")
    $$ nest 2 (vcat (map ppr ds))
    $$ text "end"
  [$me| $me1 : $se2 |] ->
    pprSigExp (pprModExp add me1 <+> colon <+>) se2
  [$me| $anti:a |] -> add (ppr a)

pprSigExp :: (Doc -> Doc) -> SigExp i -> Doc
pprSigExp add se0 = body >+> withs where
  (wts, se1) = unfoldSeWith se0
  body       = case se1 of
    [$seQ| $quid:n |] -> add (ppr n)
    [$seQ| $quid:n $list:qls |] ->
      add (ppr n) <+>
      brackets (fsep (punctuate comma (map ppr qls)))
    [$seQ| sig $list:sgs end |] ->
      add (text "sig")
      $$ nest 2 (vcat (map ppr sgs))
      $$ text "end"
    [$seQ| $_ with type $list:_ $qlid:_ = $_ |] ->
      error "BUG! can't happen in pprSigExp"
    [$seQ| $anti:a |] -> add (ppr a)
  withs      =
    sep $
      mapHead (text "with type" <+>) $
        mapTail ((nest 6) . (text "and" <+>)) $
          [ pprTyApp 0 tc tvs <+> equals <+> ppr t
          | (tc, tvs, t) <- wts ]

instance Ppr (SigItem i) where
  ppr sg0 = case sg0 of
    [$sgQ| val $lid:n : $t |] ->
      text "val" <+> ppr n >+> colon <+> ppr t
    [$sgQ| type $list:tds |] ->
      pprTyDecs tds
    [$sgQ| module $uid:u : $s |] ->
      pprSigExp add s where
        add body = text "module" <+> ppr u <+> colon <+> body
    [$sgQ| module type $uid:u = $s |] ->
      pprSigExp add s where
        add body = text "module type" <+> ppr u <+> equals <+> body
    [$sgQ| include $s |] ->
      pprSigExp (text "include" <+>) s
    [$sgQ| exception $uid:u of $opt:mt |] ->
      pprExcDec u mt
    [$sgQ| $anti:a |] ->
      ppr a

instance Ppr (Expr i) where
  pprPrec p e0 = case e0 of
    [$ex| $id:x |]   -> pprPrec p x
    [$ex| $lit:lt |] -> pprPrec p lt
    [$ex| if $ec then $et else $ef |] ->
      parensIf (p > precDot) $
        sep [ text "if" <+> ppr ec,
              nest 2 $ text "then" <+> ppr et,
              nest 2 $ text "else" <+> pprPrec precDot ef ]
    [$ex| $e1; $e2 |] ->
      parensIf (p > precSemi) $
        sep [ pprPrec (precSemi + 1) e1 <> semi,
              ppr e2 ]
    [$ex| let $x = $e1 in $e2 |] ->
      pprLet p (ppr x) e1 e2
    [$ex| match $e1 with $list:clauses |] ->
      parensIf (p > precDot) $
        vcat (sep [ text "match",
                    nest 2 $ ppr e1,
                    text "with" ] : map alt clauses)
      where
        alt (N _ (CaClause xi ei)) =
          hang (char '|' <+> pprPrec precDot xi <+> text "->")
                4
                (pprPrec precDot ei)
        alt (N _ (CaAnti a))      = char '|' <+> ppr a
    [$ex| let rec $list:bs in $e2 |] ->
      text "let" <+>
      vcat (zipWith each ("rec" : repeat "and") bs) $$
      text "in" <+> pprPrec precDot e2
        where
          each kw (N _ (BnBind x t e)) =
            -- This could be better by pulling some args out.
            hang (hang (text kw <+> ppr x)
                       6
                       (colon <+> ppr t <+> equals))
                 2
                 (ppr e)
          each kw (N _ (BnAnti a)) = text kw <+> ppr a
    [$ex| let $decl:d in $e2 |] ->
      text "let" <+> ppr d $$
      (text "in" >+> pprPrec precDot e2)
    [$ex| ($e1, $e2) |] ->
      parensIf (p > precCom) $
        sep [ pprPrec precCom e1 <> comma,
              pprPrec (precCom + 1) e2 ]
    [$ex| fun $_ : $_ -> $_ |] -> pprAbs p e0
    [$ex| $name:x $e2 |]
      | Right p' <- precOp x,
        p' == 10
          -> parensIf (p > p') $
               text x <+> pprPrec p' e2
    [$ex| ($name:x $e12) $e2 |] 
      | (dl, dr, p') <- either ((,,) 0 1) ((,,) 1 0) (precOp x),
        p' < 9
          -> parensIf (p > p') $
               sep [ pprPrec (p' + dl) e12,
                     text x,
                     pprPrec (p' + dr) e2 ]
    [$ex| $e1 $e2 |]
          -> parensIf (p > precApp) $
               sep [ pprPrec precApp e1,
                     pprPrec (precApp + 1) e2 ]
    [$ex| fun '$_ -> $_ |] -> pprAbs p e0
    [$ex| $_ [$_] |] ->
      parensIf (p > precTApp) $
        cat [ pprPrec precTApp op,
              brackets . fsep . punctuate comma $
                map (pprPrec precCom) args ]
      where 
        (args, op) = unfoldExTApp e0
    [$ex| Pack[$opt:t1]($t2, $e) |] ->
      parensIf (p > precApp) $
        text "Pack" <> maybe empty (brackets . ppr) t1 <+>
        parens (sep [ pprPrec (precCom + 1) t2 <> comma,
                      pprPrec precCom e ])
    [$ex| ( $e : $t1 :> $t2 ) |] ->
      parensIf (p > precCast) $
         sep [ pprPrec (precCast + 2) e,
               colon     <+> pprPrec (precCast + 2) t1,
               text ":>" <+> pprPrec (precCast + 2) t2 ]
    [$ex| ( $e : $t1 ) |] ->
      parensIf (p > precCast) $
         sep [ pprPrec (precCast + 2) e,
               colon     <+> pprPrec (precCast + 2) t1 ]
    [$ex| ( $e :> $t1 ) |] ->
      parensIf (p > precCast) $
         sep [ pprPrec (precCast + 2) e,
               text ":>" <+> pprPrec (precCast + 2) t1 ]
    [$ex| $anti:a |] -> pprPrec p a

pprLet :: Int -> Doc -> Expr i -> Expr i -> Doc
pprLet p pat e1 e2 = parensIf (p > precDot) $
  hang (text "let" <+> pat <+> pprArgList args <+> equals
          >+> ppr body <+> text "in")
       (if isLet (view e2)
          then 0
          else 2)
       (pprPrec precDot e2)
  where
    (args, body) = unfoldExAbs e1
    isLet (ExCase _ [_]) = True
    isLet _              = False

pprAbs :: Int -> Expr i -> Doc
pprAbs p e = parensIf (p > precDot) $
    text "fun" <+> argsDoc <+> text "->"
      >+> pprPrec precDot body
  where (args, body)   = unfoldExAbs e
        argsDoc = case args of
          [Left ([$pa| _ |], [$ty|@! unit |])]
                        -> parens empty
          [Left (x, t)] -> ppr x <+> char ':' <+> pprPrec (precArr + 1) t
          _             -> pprArgList args

pprArgList :: [Either (Patt i, Type i) (TyVar i)] -> Doc
pprArgList = fsep . map eachArg . combine where
  eachArg (Left ([$pa| _ |], [$ty|@! unit |]))
                          = parens empty
  eachArg (Left (x, t))   = parens $
                              ppr x
                                >+> colon <+> ppr t
  eachArg (Right tvs)     = brackets .
                              sep .
                                punctuate comma $
                                  map ppr tvs

  combine :: [Either a b] -> [Either a [b]]
  combine  = foldr each [] where
    each (Right b) (Right bs : es) = Right (b : bs) : es
    each (Right b) es              = Right [b] : es
    each (Left a)  es              = Left a : es

instance Ppr (Patt i) where
  pprPrec _ [$pa| _ |]             = text "_"
  pprPrec _ [$pa| $lid:l |]        = ppr l
  pprPrec _ [$pa| $quid:qu |]      = ppr qu
  pprPrec p [$pa| $quid:qu $x |]   = parensIf (p > precApp) $
                                       pprPrec precApp qu <+>
                                       pprPrec (precApp + 1) x
  pprPrec p [$pa| ($x, $y) |]      = parensIf (p > precCom) $
                                       pprPrec precCom x <> comma <+>
                                       pprPrec (precCom + 1) y
  pprPrec p [$pa| $lit:lt |]       = pprPrec p lt
  pprPrec p [$pa| $x as $lid:l |]  = parensIf (p > precDot) $
                                       pprPrec (precDot + 1) x <+>
                                       text "as" <+> ppr l
  pprPrec p [$pa| Pack('$tv,$x) |] = parensIf (p > precApp) $
                                       text "Pack" <+> parens (sep pair)
    where pair = [ pprPrec (precCom + 1) tv <> comma,
                   pprPrec precCom x ]
  pprPrec p [$pa| $anti:a |]       = pprPrec p a

instance Ppr Lit where
  ppr (LtInt i)   = integer i
  ppr (LtFloat f) = double f
  ppr (LtStr s)   = text (show s)
  ppr (LtAnti a)  = ppr a

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

instance Ppr QLit      where pprPrec = pprFromShow
instance Ppr Variance  where pprPrec = pprFromShow
instance Ppr Quant     where pprPrec = pprFromShow
instance Ppr (Lid i)   where pprPrec = pprFromShow
instance Ppr (Uid i)   where pprPrec = pprFromShow
instance Ppr (BIdent i)where pprPrec = pprFromShow
instance Ppr (TyVar i) where pprPrec = pprFromShow
instance Ppr Anti      where pprPrec = pprFromShow
instance (Show p, Show k) => Ppr (Path p k) where pprPrec = pprFromShow

-- Render a document in the preferred style, given a string continuation
renderS :: Doc -> ShowS
renderS doc rest = fullRender PageMode 80 1.5 each rest doc
  where each (Chr c) s'  = c:s'
        each (Str s) s'  = s++s'
        each (PStr s) s' = s++s'

-- Render a document in the preferred style
render :: Doc -> String
render doc = renderS doc ""

-- Render and display a document in the preferred style
printDoc :: Doc -> IO ()
printDoc = fullRender PageMode 80 1.5 each (putChar '\n')
  where each (Chr c) io  = putChar c >> io
        each (Str s) io  = putStr s >> io
        each (PStr s) io = putStr s >> io

-- Pretty-print, render and display in the preferred style
printPpr :: Ppr a => a -> IO ()
printPpr = printDoc . ppr

showFromPpr :: Ppr a => Int -> a -> ShowS
showFromPpr p t = renderS (pprPrec p t)

pprFromShow :: Show a => Int -> a -> Doc
pprFromShow p t = text (showsPrec p t "")

liftEmpty :: (Doc -> Doc -> Doc) -> Doc -> Doc -> Doc
liftEmpty joiner d1 d2
  | isEmpty d1 = d2
  | isEmpty d2 = d1
  | otherwise  = joiner d1 d2

(>+>) :: Doc -> Doc -> Doc
(>+>) = flip hang 2

(>?>) :: Doc -> Doc -> Doc
(>?>)  = liftEmpty (>+>)

infixr 5 >+>, >?>

