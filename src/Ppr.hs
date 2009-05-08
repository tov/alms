{-# OPTIONS_GHC -fno-warn-orphans #-}
module Ppr (
  Ppr(..), module Text.PrettyPrint, parensIf,
  precSemi, precCom, precDot, precArr, precStar, precApp
) where

import Syntax
import Text.PrettyPrint
import Data.List (intersperse)

class Ppr p where
  pprPrec :: Int -> p -> Doc
  ppr     :: p -> Doc

  ppr = pprPrec 0

precCast, precCom, precDot, precSemi, precArr, precStar,
  precApp, precTApp :: Int
precCast  = -1 -- :>
precCom   = -1 -- ,
precDot   =  0 -- in, else, .
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

instance Separator (Type w) where
  separator _ = comma

instance (Ppr a, Separator a) => Ppr [a] where
  pprPrec _ xs = hcat (intersperse (separator (head xs))
                                   (map (pprPrec precCom) xs))

instance Ppr (Type w) where
  -- Print sugar for arrow types:
  pprPrec p (TyCon "->" [t1, t2])
                  = parensIf (p > precArr) $
                      sep [ pprPrec (precArr + 1) t1,
                        text "->" <+> pprPrec precArr t2 ]
  pprPrec p (TyCon "-o" [t1, t2])
                  = parensIf (p > precArr) $
                      sep [ pprPrec (precArr + 1) t1,
                        text "-o" <+> pprPrec precArr t2 ]
  pprPrec p (TyCon "*" [t1, t2])
                  = parensIf (p > precStar) $
                      sep [ pprPrec precStar t1,
                        text "*" <+> pprPrec (precStar + 1) t2 ]
  pprPrec _ (TyCon n [])  = text n
  pprPrec p (TyCon n [t]) = parensIf (p > precApp) $
                              sep [ pprPrec precApp t,
                                    text n ]
  pprPrec p (TyCon n ts)  = parensIf (p > precApp) $
                              sep [ parens (pprPrec p ts),
                                    text n ]
  pprPrec p (TyVar x)     = pprPrec p x
  pprPrec p (TyAll x t)   = parensIf (p > precDot) $
                              hang (text "all" <+>
                                    fsep (map (pprPrec (precDot + 1))
                                              tvs) <>
                                    char '.')
                                   2
                                   (pprPrec precDot body)
      where (tvs, body) = unfoldTyAll (TyAll x t)
  pprPrec _ (TyA t)       = braces (pprPrec 0 t)
  pprPrec _ (TyC t)       = braces (pprPrec 0 t)

instance Ppr Prog where
  pprPrec _ (Prog ms e) = vcat (map (pprPrec 0) ms) $+$
                          hang (text "in") 2 (pprPrec 0 e)

instance Ppr Mod where
  pprPrec _ (MdC x t e) = sep
    [ text "module[C]" <+>
        pprPrec 0 x,
      nest 2 $ colon <+> pprPrec 0 t,
      nest 4 $ equals <+> pprPrec 0 e ]
  pprPrec _ (MdA x t e) = sep
    [ text "module[A]" <+>
        pprPrec 0 x,
      nest 2 $ colon <+> pprPrec 0 t,
      nest 4 $ equals <+> pprPrec 0 e ]
  pprPrec _ (MdInt x t y)      = sep
    [ text "interface" <+> pprPrec 0 x,
      nest 2 $ text ":>" <+> pprPrec 0 t,
      nest 4 $ equals <+> pprPrec 0 y ]

instance Ppr (Expr w) where
  pprPrec p e0 = case expr' e0 of
    ExCon s -> text s
    ExInt i -> integer i
    ExStr s -> text (show s)
    ExIf ec et ef ->
      parensIf (p > precDot) $
        sep [ text "if" <+> pprPrec 0 ec,
              nest 2 $ text "then" <+> pprPrec 0 et,
              nest 2 $ text "else" <+> pprPrec precDot ef ]
    ExCase e1 (xl, el) (xr, er) ->
      parensIf (p > precDot) $
        vcat [ sep [ text "match", nest 2 $ pprPrec 0 e1, text "with" ],
               alt "Left" xl el,
               alt "Right" xr er ]
        where
          alt cons xi ei =
            hang (char '|' <+> text cons <+>
                  pprPrec (precApp + 1) xi <+> text "->")
                  4
                  (pprPrec precDot ei)
    ExLet x e1 e2 ->
      pprLet p (pprPrec 0 x) e1 e2
    ExVar x -> pprPrec 0 x
    ExPair e1 e2 ->
      parensIf (p > precCom) $
        sep [ pprPrec (precCom + 1) e1 <> comma,
              pprPrec (precCom + 1) e2 ]
    ExLetPair (x, y) e1 e2 ->
      pprLet p (parens (pprPrec 0 x <> comma <+> pprPrec 0 y)) e1 e2
    ExAbs _ _ _ -> pprAbs p e0
    ExApp e1 e2 ->
      parensIf (p > precApp) $
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
    ExSeq e1 e2 ->
      parensIf (p > precSemi) $
        sep [ pprPrec (precSemi + 1) e1 <> semi,
              pprPrec 0 e2 ]
    ExCast e t1 t2 ->
      parensIf (p > precCast) $
        sep [ pprPrec (precCast + 1) e,
              colon,
              pprPrec (precCast + 1) t1,
              text ":>",
              pprPrec (precCast + 1) t2 ]

pprLet :: Int -> Doc -> Expr w -> Expr w -> Doc
pprLet p pat e1 e2 = parensIf (p > precDot) $
  sep [ text "let" <+> pat <+>
        pprArgList args <+>
        equals <+> pprPrec 0 body <+> text "in",
        nest (if isLet (expr' e2)
                then 0
                else 2)
             (pprPrec precDot e2) ]
  where
    isLet (ExLet _ _ _)     = True
    isLet (ExLetPair _ _ _) = True
    isLet _                 = False
    (args, body) = unfoldExAbs e1

pprAbs :: Int -> Expr w -> Doc
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

pprArgList :: [Either (Var, Type w) TyVar] -> Doc
pprArgList = fsep . map eachArg where
  eachArg (Left (x, t))   = parens $ hang
                              (pprPrec 0 x)
                              2
                              (colon <+> pprPrec 0 t)
  eachArg (Right tv)      = pprPrec 0 tv

instance Show Prog     where showsPrec = showFromPpr
instance Show Mod      where showsPrec = showFromPpr
instance Show (Expr w) where showsPrec = showFromPpr
instance Show (Type w) where showsPrec = showFromPpr

instance Ppr Variance  where pprPrec = pprFromShow
instance Ppr Var       where pprPrec = pprFromShow
instance Ppr TyVar     where pprPrec = pprFromShow

showFromPpr :: Ppr a => Int -> a -> ShowS
showFromPpr p t = shows (pprPrec p t)

pprFromShow :: Show a => Int -> a -> Doc
pprFromShow p t = text (showsPrec p t "")

