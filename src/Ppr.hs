-- | Pretty-printing
{-# LANGUAGE
      PatternGuards,
      QuasiQuotes
    #-}
module Ppr (
  -- * Pretty-printing class
  Ppr(..),
  -- * Pretty-printing combinators
  parensIf,
  -- * Instance helpers
  showFromPpr, pprFromShow,
  -- * Re-exports
  module Text.PrettyPrint,
  module Prec
) where

import Prec
import Quasi
import Syntax

import Text.PrettyPrint
import Data.List (intersperse)
import Data.Typeable (Typeable, cast)

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

  ppr       = pprPrec precDot
  pprPrec _ = ppr

-- | Conditionally add parens around the given 'Doc'
parensIf :: Bool -> Doc -> Doc
parensIf True  doc = parens doc
parensIf False doc = doc

class Separator a where
  separator :: a -> Doc

instance Separator (Type i) where
  separator _ = comma

instance (Ppr a, Separator a) => Ppr [a] where
  ppr xs = hcat (intersperse (separator (head xs))
                             (map (pprPrec precCom) xs))

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
                          pprArr q <+> pprPrec precArr t2 ]
    where pprArr (QeLit Qu) = text "->"
          pprArr (QeLit Qa) = text "-o"
          pprArr _          = text "-[" <> pprPrec precStart q <> text "]>"
  pprPrec p [$ty| ($t1, $t2) $name:n |]
    | isOperator (Lid n)
                  = case precOp n of
        Left prec  -> parensIf (p > prec) $
                      sep [ pprPrec prec t1,
                            text n <+> pprPrec (prec + 1) t2 ]
        Right prec -> parensIf (p > prec) $
                      sep [ pprPrec (prec + 1) t1,
                            text n <+> pprPrec prec t2]
  pprPrec _ [$ty| $qlid:n |]  = ppr n
    -- debugging: <> text (show (ttId (unsafeCoerce tag :: TyTag)))
  pprPrec p [$ty| $t $qlid:n |]
                              = parensIf (p > precApp) $
                                sep [ pprPrec precApp t,
                                      ppr n ]
  pprPrec p [$ty| ($list:ts) $qlid:n |]
                          = parensIf (p > precApp) $
                                sep [ parens (ppr ts),
                                      ppr n ]
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

instance (Typeable a, Ppr a) => Ppr (QExp a) where
  pprPrec p (QeLit qu)    = pprPrec p qu
  pprPrec p (QeVar v)     = case cast v of
    Just (TV lid Qa)  -> pprPrec p lid
    _                 -> pprPrec p v
  pprPrec p (QeDisj [])   = pprPrec p Qu
  pprPrec p (QeDisj [qe]) = pprPrec p qe
  pprPrec p (QeDisj qes)  = parensIf (p > precPlus) $
                              fsep $
                                intersperse (text "\\/") $
                                  map (pprPrec (precPlus + 1)) qes
  pprPrec p (QeConj [])   = pprPrec p Qa
  pprPrec p (QeConj [qe]) = pprPrec p qe
  pprPrec p (QeConj qes)  = parensIf (p > precStar) $
                              hcat $
                                intersperse (text "/\\") $
                                  map (pprPrec (precStar + 1)) qes
  pprPrec p (QeAnti a)    = pprPrec p a

instance Ppr Int where
  ppr = int

instance Ppr (Prog i) where
  ppr [$pr| $list:ms |]       = vcat (map ppr ms)
  ppr [$pr| $expr:e |]        = ppr e
  ppr [$pr| $list:ms in $e |] = vcat (map ppr ms) $+$
                                 (text "in" >+> ppr e)

instance Ppr (Decl i) where
  ppr [$dc| let $x = $e |] = sep
    [ text "let" <+> ppr x,
      nest 2 $ equals <+> ppr e ]
  ppr [$dc| let $x : $t = $e |] = sep
    [ text "let" <+> ppr x,
      nest 2 $ colon <+> ppr t,
      nest 4 $ equals <+> ppr e ]
  ppr [$dc| type $list:tds0 |]
    | td:tds <- tds0 =
    vcat $
      text "type" <+> ppr td :
      [ nest 1 $ text "and" <+> ppr td' | td' <- tds ]
    | otherwise      = empty
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
          vcat (text "abstype" <> pprAbsTy at :
                [ nest 4 $ text "and" <+> pprAbsTy ati | ati <- ats ])
            <+> text "with",
          nest 2 $ vcat (map ppr ds),
          text "end"
        ]
  ppr [$dc| open $b |] = pprModExp (text "open" <+>) b
  ppr [$dc| module $uid:n = $b |] = pprModExp add b where
    add body = text "module" <+> ppr n <+> equals <+> body
  ppr [$dc| local $list:d0 with $list:d1 end |] =
    vcat [
      text "local",
      nest 2 (vcat (map ppr d0)),
      text "with",
      nest 2 (vcat (map ppr d1)),
      text "end"
    ]
  ppr [$dc| exception $uid:n |] =
    text "exception" <+> ppr n
  ppr [$dc| exception $uid:n of $t |] =
    text "exception" <+> ppr n <+> text "of" <+> ppr t
  ppr [$dc| $anti:a |] = ppr a

instance Ppr (TyDec i) where
  ppr (TdAbs n ps vs qs) = pprProtoV n vs ps >?> pprQuals qs
  ppr (TdSyn n ps rhs)   = pprProto n ps >?> equals <+> ppr rhs
  ppr (TdDat n ps alts)  = pprProto n ps >?> pprAlternatives alts
  ppr (TdAnti a)         = ppr a

pprAbsTy :: AbsTy i -> Doc
pprAbsTy (AbsTy variances qual (TdDat name params alts)) =
    pprProtoV name variances params
      >?> pprQuals qual
      >?> pprAlternatives alts
pprAbsTy (AbsTy _ _ td) = ppr td -- shouldn't happen (yet)
pprAbsTy (AbsTyAnti a) = ppr a

pprProto     :: Lid -> [TyVar] -> Doc
pprProto n [tv1, tv2]
  | isOperator n = ppr tv1 <+> text (unLid n) <+> ppr tv2
pprProto n tvs   = pprParams tvs <?> ppr n

pprProtoV     :: Lid -> [Variance] -> [TyVar] -> Doc
pprProtoV n [v1, v2] [tv1, tv2]
  | isOperator n   = ppr v1 <> ppr tv1 <+>
                     text (unLid n)    <+>
                     ppr v2 <> ppr tv2
pprProtoV n vs tvs = pprParamsV vs tvs <?> ppr n

-- | Print a list of type variables as printed as the parameters
--   to a type.
pprParams    :: [TyVar] -> Doc
pprParams tvs = delimList parens comma (map ppr tvs)

pprParamsV       :: [Variance] -> [TyVar] -> Doc
pprParamsV vs tvs = delimList parens comma (zipWith pprParam vs tvs)
  where
    pprParam Invariant tv = ppr tv
    pprParam v         tv = ppr v <> ppr tv

pprQuals :: (Typeable a, Ppr a) => QExp a -> Doc
pprQuals (QeLit Qu) = empty
pprQuals qs         = text "qualifier" <+> pprPrec precApp qs

pprAlternatives :: [(Uid, Maybe (Type i))] -> Doc
pprAlternatives [] = equals
pprAlternatives (a:as) = sep $
  equals <+> alt a : [ char '|' <+> alt a' | a' <- as ]
  where
    alt (Uid s, Nothing) = text s
    alt (Uid s, Just t)  = text s <+> text "of" <+> pprPrec precDot t

pprModExp :: (Doc -> Doc) -> ModExp i -> Doc
pprModExp add modexp = case modexp of
  [$me| $quid:n |] -> add (ppr n)
  [$me| struct $list:ds end |] ->
    add (text "struct")
    $$ nest 2 (vcat (map ppr ds))
    $$ text "end"
  [$me| $anti:a |] -> add (ppr a)

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
    [$ex| let $lid:x = $e1 in $e2 |] ->
      pprLet p (ppr x) e1 e2
    [$ex| match $e1 with $list:clauses |] ->
      parensIf (p > precDot) $
        vcat (sep [ text "match",
                    nest 2 $ ppr e1,
                    text "with" ] : map alt clauses)
      where
        alt (CaseAlt xi ei) =
          hang (char '|' <+> pprPrec precDot xi <+> text "->")
                4
                (pprPrec precDot ei)
        alt (CaAnti a)      = char '|' <+> ppr a
    [$ex| let rec $list:bs in $e2 |] ->
      text "let" <+>
      vcat (zipWith each ("rec" : repeat "and") bs) $$
      text "in" <+> pprPrec precDot e2
        where
          each kw (Binding x t e) =
            -- This could be better by pulling some args out.
            hang (hang (text kw <+> ppr x)
                       6
                       (colon <+> ppr t <+> equals))
                 2
                 (ppr e)
          each kw (BnAnti a) = text kw <+> ppr a
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
    [$ex| ( $e : $opt:t1 :> $t2 ) |] ->
      parensIf (p > precCast) $
        sep (pprPrec (precCast + 2) e :
             maybe [] (\t1' -> [
               colon,
               pprPrec (precCast + 2) t1'
             ]) t1 ++
             [ text ":>",
               pprPrec (precCast + 2) t2 ])
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
          [Left ([$pa| _ |], [$ty| unit |])]
                        -> parens empty
          [Left (x, t)] -> ppr x <+> char ':' <+> pprPrec (precArr + 1) t
          _             -> pprArgList args

pprArgList :: [Either (Patt i, Type i) TyVar] -> Doc
pprArgList = fsep . map eachArg . combine where
  eachArg (Left ([$pa| _ |], [$ty| unit |]))
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
  pprPrec _ [$pa| $lid:lid |]      = ppr lid
  pprPrec _ [$pa| $quid:qu |]      = ppr qu
  pprPrec p [$pa| $quid:qu $x |]   = parensIf (p > precApp) $
                                       pprPrec precApp qu <+>
                                       pprPrec (precApp + 1) x
  -- ICK!  TODO: get rid of the next two cases:
  pprPrec _ [$pa| $quid:qu !!! |]  = ppr qu
  pprPrec p [$pa| $quid:qu $x !!! |]
                                   = parensIf (p > precApp) $
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
instance (Typeable a, Ppr a) =>
         Show (QExp a)   where showsPrec = showFromPpr

instance Ppr QLit      where pprPrec = pprFromShow
instance Ppr Variance  where pprPrec = pprFromShow
instance Ppr Quant     where pprPrec = pprFromShow
instance Ppr Lid       where pprPrec = pprFromShow
instance Ppr Uid       where pprPrec = pprFromShow
instance Ppr BIdent    where pprPrec = pprFromShow
instance Ppr TyVar     where pprPrec = pprFromShow
instance Ppr Anti      where pprPrec = pprFromShow
instance (Show p, Show k) => Ppr (Path p k) where pprPrec = pprFromShow

showFromPpr :: Ppr a => Int -> a -> ShowS
showFromPpr p t = shows (pprPrec p t)

pprFromShow :: Show a => Int -> a -> Doc
pprFromShow p t = text (showsPrec p t "")

delimList :: (Doc -> Doc) -> Doc -> [Doc] -> Doc
delimList around delim ds = case ds of
  []  -> empty
  [d] -> d
  _   -> around . fsep . punctuate delim $ ds

liftEmpty :: (Doc -> Doc -> Doc) -> Doc -> Doc -> Doc
liftEmpty joiner d1 d2
  | isEmpty d1 = d2
  | isEmpty d2 = d1
  | otherwise  = joiner d1 d2

(<?>) :: Doc -> Doc -> Doc
(<?>)  = liftEmpty (<+>)

(>+>) :: Doc -> Doc -> Doc
(>+>) = flip hang 2

(>?>) :: Doc -> Doc -> Doc
(>?>)  = liftEmpty (>+>)

infixr 6 <?>
infixr 5 >+>, >?>

