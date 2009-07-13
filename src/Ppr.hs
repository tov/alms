{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Ppr (
  Ppr(..), module Text.PrettyPrint, parensIf,
  precSemi, precCom, precDot, precArr, precStar, precApp
) where

import Syntax
import Lexer (precOp)
import Text.PrettyPrint
import Data.List (intersperse)

class Ppr p where
  pprPrec :: Int -> p -> Doc
  ppr     :: p -> Doc

  ppr = pprPrec 0

precCast, precCom, precDot, precSemi, precArr, precStar,
  precApp, precTApp :: Int
precCast  = -2 -- :>
precCom   = -1 -- ,
precDot   =  0 -- in, else, as, of, .
precSemi  =  1 -- ;
precArr   =  5 -- ->
precStar  =  6 -- *
precApp   =  9 -- f x
precTApp  = 10 -- f[t]

parensIf :: Bool -> Doc -> Doc
parensIf True  doc = parens doc
parensIf False doc = doc

class Separator a where
  separator :: a -> Doc

instance Separator (Type i w) where
  separator _ = comma

instance (Ppr a, Separator a) => Ppr [a] where
  pprPrec _ xs = hcat (intersperse (separator (head xs))
                                   (map (pprPrec precCom) xs))

instance Ppr (Type i w) where
  -- Print sugar for arrow types:
  pprPrec p (TyCon (Lid "->") [t1, t2] _)
                  = parensIf (p > precArr) $
                      sep [ pprPrec (precArr + 1) t1,
                        text "->" <+> pprPrec precArr t2 ]
  pprPrec p (TyCon (Lid "-o") [t1, t2] _)
                  = parensIf (p > precArr) $
                      sep [ pprPrec (precArr + 1) t1,
                        text "-o" <+> pprPrec precArr t2 ]
  pprPrec p (TyCon (Lid "*") [t1, t2] _)
                  = parensIf (p > precStar) $
                      sep [ pprPrec precStar t1,
                        text "*" <+> pprPrec (precStar + 1) t2 ]
  pprPrec _ (TyCon n [] _)  = ppr n
  pprPrec p (TyCon n [t] _) = parensIf (p > precApp) $
                                sep [ pprPrec precApp t,
                                      ppr n ]
  pprPrec p (TyCon n ts _)  = parensIf (p > precApp) $
                                sep [ parens (pprPrec p ts),
                                      ppr n ]
  pprPrec p (TyVar x)     = pprPrec p x
  pprPrec p (TyAll x t)   = parensIf (p > precDot) $
                              hang (text "all" <+>
                                    fsep (map (pprPrec (precDot + 1))
                                              tvs) <>
                                    char '.')
                                   2
                                   (pprPrec precDot body)
      where (tvs, body) = unfoldTyAll (TyAll x t)
  pprPrec p (TyMu x t)    = parensIf (p > precDot) $
                              hang (text "mu" <+>
                                    pprPrec (precDot + 1) x <>
                                    char '.')
                                   2
                                   (pprPrec precDot t)
  pprPrec _ (TyA t)       = braces (pprPrec 0 t)
  pprPrec _ (TyC t)       = braces (pprPrec 0 t)

instance Ppr (Prog i) where
  pprPrec _ (Prog ms e) = vcat (map (pprPrec 0) ms) $+$
                          hang (text "in") 2 (pprPrec 0 e)

instance Ppr (Decl i) where
  pprPrec p (DcMod m)  = pprPrec p m
  pprPrec p (DcTyp td) = pprPrec p td

instance Ppr (Mod i) where
  pprPrec _ (MdC x Nothing e) = sep
    [ text "module[C]" <+> pprPrec 0 x,
      nest 2 $ equals <+> pprPrec 0 e ]
  pprPrec _ (MdA x Nothing e) = sep
    [ text "module[A]" <+> pprPrec 0 x,
      nest 2 $ equals <+> pprPrec 0 e ]
  pprPrec _ (MdC x (Just t) e) = sep
    [ text "module[C]" <+>
        pprPrec 0 x,
      nest 2 $ colon <+> pprPrec 0 t,
      nest 4 $ equals <+> pprPrec 0 e ]
  pprPrec _ (MdA x (Just t) e) = sep
    [ text "module[A]" <+>
        pprPrec 0 x,
      nest 2 $ colon <+> pprPrec 0 t,
      nest 4 $ equals <+> pprPrec 0 e ]
  pprPrec _ (MdInt x t y)      = sep
    [ text "interface" <+> pprPrec 0 x,
      nest 2 $ text ":>" <+> pprPrec 0 t,
      nest 4 $ equals <+> pprPrec 0 y ]

instance Ppr (TyDec i) where
  pprPrec _ (TdAbsA n ps vs qs) = addQuals qs $
    text "type[A]" <?>
    delimList parens comma (zipWith pprParam ps vs) <+>
    ppr n
    where
      pprParam v tv = pprPrec 0 v <> pprPrec 0 tv
      addQuals [] doc = doc
      addQuals _  doc = hang doc 2 $
        text "qualifier" <+>
        delimList parens (text " \\/") (map (either ppr ppr) qs)
  pprPrec _ (TdAbsC n ps) =
    text "type[C]" <?>
    delimList parens comma (map ppr ps) <+>
    ppr n
  pprPrec _ (TdSynA n ps rhs) =
    hang (text "type[A]" <?>
          delimList parens comma (map ppr ps) <+>
          ppr n)
         2
         (equals <+>
          pprPrec 0 rhs)
  pprPrec _ (TdSynC n ps rhs) =
    hang (text "type[C]" <?>
          delimList parens comma (map ppr ps) <+>
          ppr n)
         2
         (equals <+>
          pprPrec 0 rhs)
  pprPrec _ (TdDatC n ps alts) =
    hang (text "type[C]" <?>
          delimList parens comma (map ppr ps) <+>
          ppr n)
         2
         (pprAlternatives alts)
  pprPrec _ (TdDatA n ps alts) =
    hang (text "type[A]" <?>
          delimList parens comma (map ppr ps) <+>
          ppr n)
         2
         (pprAlternatives alts)

pprAlternatives :: [(Uid, Maybe (Type i w))] -> Doc
pprAlternatives [] = equals
pprAlternatives (a:as) = sep $
  equals <+> alt a : [ char '|' <+> alt a' | a' <- as ]
  where
    alt (Uid s, Nothing) = text s
    alt (Uid s, Just t)  = text s <+> text "of" <+> pprPrec precDot t

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
infixl 6 <?>

instance Ppr (Expr i w) where
  pprPrec p e0 = case expr' e0 of
    ExId x  -> pprPrec 0 x
    ExInt i -> integer i
    ExStr s -> text (show s)
    ExCase e1 clauses ->
      case clauses of
        [ (PaCon (Uid "true")  Nothing, et),
          (PaCon (Uid "false") Nothing, ef) ] ->
            parensIf (p > precDot) $
              sep [ text "if" <+> pprPrec 0 e1,
                    nest 2 $ text "then" <+> pprPrec 0 et,
                    nest 2 $ text "else" <+> pprPrec precDot ef ]
        [ (PaWild, e2) ] ->
            parensIf (p > precSemi) $
              sep [ pprPrec (precSemi + 1) e1 <> semi,
                    pprPrec 0 e2 ]
        [ (x, e2) ] ->
            pprLet p (pprPrec 0 x) e1 e2
        _ ->
            parensIf (p > precDot) $
              vcat (sep [ text "match",
                          nest 2 $ pprPrec 0 e1,
                          text "with" ] : map alt clauses)
            where
              alt (xi, ei) =
                hang (char '|' <+> pprPrec precDot xi <+> text "->")
                      4
                      (pprPrec precDot ei)
    ExLetRec bs e2 ->
      text "let" <+>
      vcat (zipWith each ("rec" : repeat "and") bs) $$
      text "in" <+> pprPrec precDot e2
        where
          each kw (Binding x t e) =
            -- This could be better by pulling some args out.
            hang (hang (text kw <+> pprPrec 0 x)
                       6
                       (colon <+> pprPrec 0 t <+> equals))
                 2
                 (pprPrec 0 e)
    ExPair e1 e2 ->
      parensIf (p > precCom) $
        sep [ pprPrec precCom e1 <> comma,
              pprPrec (precCom + 1) e2 ]
    ExAbs _ _ _ -> pprAbs p e0
    ExApp e1 e2
      | ExId (Var (Lid x)) <- expr' e1,
        Right p'           <- precOp x,
        p' == 8
          -> parensIf (p > p') $
               text x <+> pprPrec p' e2
      | ExApp e11 e12      <- expr' e1,
        ExId (Var (Lid x)) <- expr' e11,
        (pl, pr, p')       <- either ((,,) 0 1) ((,,) 1 0) (precOp x),
        p' <= 8
          -> parensIf (p > p') $
               sep [ pprPrec (p' + pl) e12,
                     text x,
                     pprPrec (p' + pr) e2 ]
      | otherwise
          -> parensIf (p > precApp) $
               sep [ pprPrec precApp e1,
                     pprPrec (precApp + 1) e2 ]
    ExTAbs _ _  -> pprAbs p e0
    ExTApp _ _  ->
      parensIf (p > precTApp) $
        cat [ pprPrec precTApp op,
              brackets . fsep . punctuate comma $
                map (pprPrec precCom) args ]
      where 
        (args, op) = unfoldExTApp e0
    ExCast e t1 t2 ->
      parensIf (p > precCast) $
        sep [ pprPrec (precCast + 2) e,
              colon,
              pprPrec (precCast + 2) t1,
              text ":>",
              pprPrec (precCast + 2) t2 ]

pprLet :: Int -> Doc -> Expr i w -> Expr i w -> Doc
pprLet p pat e1 e2 = parensIf (p > precDot) $
  hang (hang (text "let" <+> pat <+> pprArgList args <+> equals)
             2
             (pprPrec 0 body <+> text "in"))
       (if isLet (expr' e2)
          then 0
          else 2)
       (pprPrec precDot e2)
  where
    (args, body) = unfoldExAbs e1
    isLet (ExCase _ [_]) = True
    isLet _              = False

pprAbs :: Int -> Expr i w -> Doc
pprAbs p e = parensIf (p > precDot) $
  hang
    (addArgs (char '\\') <> char '.')
    2
    (pprPrec precDot body)
  where (args, body)   = unfoldExAbs e
        addArgs = case args of
          [Left (x, t)] -> (<> (pprPrec 0 x <+>
                                char ':' <+> pprPrec 0 t))
          _             -> (<>  pprArgList args)

pprArgList :: [Either (Patt, Type i w) TyVar] -> Doc
pprArgList = fsep . map eachArg where
  eachArg (Left (x, t))   = parens $ hang
                              (pprPrec 0 x)
                              2
                              (colon <+> pprPrec 0 t)
  eachArg (Right tv)      = pprPrec 0 tv

instance Ppr Patt where
  pprPrec _ PaWild               = text "_"
  pprPrec _ (PaVar lid)          = ppr lid
  pprPrec _ (PaCon uid Nothing)  = ppr uid
  pprPrec p (PaCon uid (Just x)) = parensIf (p > precApp) $
                                     pprPrec precApp uid <+>
                                     pprPrec (precApp + 1) x
  pprPrec p (PaPair x y)         = parensIf (p > precCom) $
                                     pprPrec precCom x <> comma <+>
                                     pprPrec (precCom + 1) y
  pprPrec _ (PaStr s)            = text (show s)
  pprPrec _ (PaInt z)            = text (show z)
  pprPrec p (PaAs x lid)         = parensIf (p > precDot) $
                                     pprPrec (precDot + 1) x <+>
                                     text "as" <+> ppr lid

instance Show (Prog i)   where showsPrec = showFromPpr
instance Show (Decl i)   where showsPrec = showFromPpr
instance Show (Mod i)    where showsPrec = showFromPpr
instance Show (TyDec i)  where showsPrec = showFromPpr
instance Show (Expr i w) where showsPrec = showFromPpr
instance Show Patt       where showsPrec = showFromPpr
instance Show (Type i w) where showsPrec = showFromPpr

instance Ppr Q         where pprPrec = pprFromShow
instance Ppr Variance  where pprPrec = pprFromShow
instance Ppr Lid       where pprPrec = pprFromShow
instance Ppr Uid       where pprPrec = pprFromShow
instance Ppr Ident     where pprPrec = pprFromShow
instance Ppr TyVar     where pprPrec = pprFromShow

instance Show TypeTW where
  showsPrec p (TypeTA t) = showsPrec p t
  showsPrec p (TypeTC t) = showsPrec p t

showFromPpr :: Ppr a => Int -> a -> ShowS
showFromPpr p t = shows (pprPrec p t)

pprFromShow :: Show a => Int -> a -> Doc
pprFromShow p t = text (showsPrec p t "")

