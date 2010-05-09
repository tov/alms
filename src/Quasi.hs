{-# LANGUAGE
      FlexibleInstances,
      RelaxedPolyRec,
      PatternGuards,
      QuasiQuotes,
      RankNTypes,
      ScopedTypeVariables,
      TemplateHaskell,
      TypeSynonymInstances #-}
module Quasi (
  pa, ty, ex, dc, pr, me
) where

import Loc as Loc
import Parser
import Util

import QuoteData
import Syntax
import Syntax.THQuasi

import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote (QuasiQuoter(..))

pa, ty, ex, dc, pr, me :: QuasiQuoter

ex  = mkQuasi parseExpr $ \ast loc -> [| $(ast) <<@ $(mkvarE loc) |]
dc  = mkQuasi parseDecl $ \ast loc -> [| $(ast) <<@ $(mkvarE loc) |]
ty  = mkQuasi parseType const
pr  = mkQuasi parseProg const
me  = mkQuasi parseModExp const
pa  = mkQuasi parsePatt const

mkQuasi :: forall f. (Data (f ())) =>
      (forall i. Id i => P (f i)) ->
      (TH.ExpQ -> String -> TH.ExpQ) ->
      QuasiQuoter
mkQuasi parser reloc = QuasiQuoter qexp qpat where
  qexp s = do
    (stx, lflag) <- parseQuasi s $ \_ lflag -> do
      stx <- parser :: P (f ())
      return (stx, lflag)
    ast <- toExpQ stx
    case lflag of
      Just loc -> reloc (return ast) loc
      Nothing  -> return ast
  qpat s = do
    (stx, lflag) <- parseQuasi s $ \_ lflag -> do
      stx <- parser :: P (f ())
      return (stx, lflag)
    ast <- toPatQ stx
    case (lflag, ast) of
      (Just loc, TH.RecP n fs)
             -> TH.recP n (TH.fieldPat 'eloc_
                                       (mkvarP loc) : map return fs)
      (Just loc, TH.ConP n (TH.WildP:ps))
             -> TH.conP n (mkvarP loc : map return ps)
      (_, _) -> return ast

toExpQ :: Data a => a -> TH.ExpQ
toExpQ  = dataToExpQ antiExp moduleQuals

toPatQ :: Data a => a -> TH.PatQ
toPatQ  = dataToPatQ antiPat moduleQuals

moduleQuals :: [(String, String)]
moduleQuals  = [ ("Syntax.Type", "Syntax") ]

antiExp :: Data a => a -> Maybe TH.ExpQ
antiExp  = antiGen
           `ext1Q` expToExpQ

antiPat :: Data a => a -> Maybe TH.PatQ
antiPat  = antiGen
           `ext1Q` expToPatQ
           `extQ`  antiLocPat
           `extQ`  antiUnitPat

antiGen :: forall a b. (Data a, ToSyntax b) => a -> Maybe (TH.Q b)
antiGen  = $(expandAntible ''Lit)
         . $(expandAntible ''Patt)
         . $(expandAntible ''Binding)
         . $(expandAntible ''CaseAlt)
         . $(expandAntible ''Type)
         . $(expandAntible ''Quant)
         . $(expandAntibleType [t| QExp Int |])
         . $(expandAntibleType [t| QExp TyVar |])
         . $(expandAntible ''TyVar)
         . $(expandAntible ''Decl)
         . $(expandAntible ''TyDec)
         . $(expandAntible ''AbsTy)
         . $(expandAntible ''ModExp)
         . $(expandAntible ''Lid)
         . $(expandAntible ''Uid)
         . $(expandAntible ''QLid)
         . $(expandAntible ''QUid)
         . $(expandAntible ''Ident)
         $ const Nothing

antiLocPat :: Loc.Loc -> Maybe TH.PatQ
antiLocPat _ = Just TH.wildP

antiUnitPat :: () -> Maybe TH.PatQ
antiUnitPat _ = Just TH.wildP

expToExpQ :: Data i => Expr i -> Maybe TH.ExpQ
expToExpQ = Just . loop where
  loop e0 = case view e0 of
    ExAnti a      -> fromJust . $(expandAnti 'ExAnti 'exprAntis) $ ExAnti a
    ExId i        -> [| exId $(toExpQ i) |]
    ExLit lt      -> [| exLit $(toExpQ lt) |]
    ExCase e bs   -> [| exCase $(loop e) $(toExpQ bs) |]
    ExLetRec bs e -> [| exLetRec $(toExpQ bs)$ $(loop e) |]
    ExLetDecl d e -> [| exLetDecl $(toExpQ d) $(loop e) |]
    ExPair e1 e2  -> [| exPair $(loop e1) $(loop e2) |]
    ExAbs x t e   -> [| exAbs $(toExpQ x) $(toExpQ t) $(loop e) |]
    ExApp e1 e2   -> [| exApp $(loop e1) $(loop e2) |]
    ExTAbs tv e   -> [| exTAbs $(toExpQ tv) $(loop e) |]
    ExTApp e t    -> [| exTApp $(loop e) $(toExpQ t) |]
    ExPack mt t e -> [| exPack $(toExpQ mt) $(toExpQ t) $(loop e) |]
    ExCast e mt t -> [| exCast $(loop e) $(toExpQ mt) $(toExpQ t) |]

expToPatQ :: Data i => Expr i -> Maybe TH.PatQ
expToPatQ e0 = Just body where
  body = case view e0 of
    ExAnti a -> fromJust . $(expandAnti 'ExAnti 'exprAntis) $ ExAnti a
    e        -> TH.recP 'Expr [TH.fieldPat 'expr_ (toPatQ e)]

---
--- Syntax helpers
---

mkvarE :: String -> TH.ExpQ
mkvarE  = TH.varE . TH.mkName

mkvarP :: String -> TH.PatQ
mkvarP "_" = TH.wildP
mkvarP n   = TH.varP (TH.mkName n)
