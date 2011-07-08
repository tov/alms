{-# LANGUAGE
      FlexibleContexts,
      FlexibleInstances,
      QuasiQuotes,
      RankNTypes,
      ScopedTypeVariables,
      TemplateHaskell,
      TypeSynonymInstances #-}
module Meta.Quasi (
  pa, ty, ex, dc, me,
  prQ, tdQ, atQ, caQ, bnQ, qeQ, tpQ, seQ, sgQ,
) where

import Meta.QuoteData
import Meta.THHelpers
import Parser
import Syntax
import Util

import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote (QuasiQuoter(..))

toAstQ :: (Data a, ToSyntax b) => a -> TH.Q b
toAstQ x = whichS' (toExpQ False x) (toPatQ False x)

toAstQ' :: (Data a, ToSyntax b) => a -> TH.Q b
toAstQ' x = whichS' (toExpQ True x) (toPatQ True x)

toExpQ :: Data a => Bool -> a -> TH.ExpQ
toExpQ False x = dataToExpQ antiExp moduleQuals x
toExpQ True  x = do
  TH.AppE _ stx <- dataToExpQ antiExp moduleQuals x
  return stx

toPatQ :: Data a => Bool -> a -> TH.PatQ
toPatQ False x = dataToPatQ antiPat moduleQuals x
toPatQ True  x = do
  TH.ConP _ [_, stx] <- dataToPatQ antiPat moduleQuals x
  return stx

moduleQuals :: [(String, String)]
moduleQuals  = [ ("Syntax.Type", "Syntax") ]

antiExp :: Data a => a -> Maybe TH.ExpQ
antiExp  = antiGen

antiPat :: Data a => a -> Maybe TH.PatQ
antiPat  = antiGen
           `extQ`  antiLocPat
           `extQ`  antiUnitPat
           `extQ`  antiRawPat

antiGen :: forall a b. (Data a, ToSyntax b) => a -> Maybe (TH.Q b)
antiGen  = $(expandAntibles [''Raw, ''Renamed] 'toAstQ syntaxTable)
         $ const Nothing

antiLocPat :: Loc -> Maybe TH.PatQ
antiLocPat _ = Just TH.wildP

antiUnitPat :: () -> Maybe TH.PatQ
antiUnitPat _ = Just TH.wildP

antiRawPat :: Raw -> Maybe TH.PatQ
antiRawPat _ = Just TH.wildP

---
--- Syntax helpers
---

mkvarE :: String -> TH.ExpQ
mkvarE  = TH.varE . TH.mkName

mkvarP :: String -> TH.PatQ
mkvarP "_" = TH.wildP
mkvarP n   = TH.varP (TH.mkName n)

---
--- Quasiquoters
---

pa, ty, ex, dc, me, prQ, tdQ, atQ, caQ, bnQ, qeQ, tpQ, seQ, sgQ
  :: QuasiQuoter

ex  = mkQuasi "ex" parseExpr
dc  = mkQuasi "dc" parseDecl
ty  = mkQuasi "ty" parseType
me  = mkQuasi "me" parseModExp
pa  = mkQuasi "pa" parsePatt
prQ = mkQuasi "prQ" parseProg
tdQ = mkQuasi "tdQ" parseTyDec
atQ = mkQuasi "atQ" parseAbsTy
caQ = mkQuasi "caQ" parseCaseAlt
bnQ = mkQuasi "bnQ" parseBinding
qeQ = mkQuasi "qeQ" parseQExp
tpQ = mkQuasi "tpQ" parseTyPat
seQ = mkQuasi "seQ" parseSigExp
sgQ = mkQuasi "sgQ" parseSigItem

mkQuasi :: forall stx note.
           (Data (note Raw), Data (stx Raw),
            LocAst (N (note Raw) (stx Raw)),
            Data (note Renamed), Data (stx Renamed),
            LocAst (N (note Renamed) (stx Renamed))) =>
           String ->
           (forall i. Id i => P (N (note i) (stx i))) ->
           QuasiQuoter
mkQuasi name parser = (newQuasi name) { quoteExp = qast, quotePat = qast }
  where
  qast s =
    join $
      parseQuasi s $ \filename iflag lflag ->
        case iflag of
          "+'" -> do
            stx <- parser :: P (N (note Renamed) (stx Renamed))
            convert' filename stx
          "+" -> do
            stx <- parser :: P (N (note Renamed) (stx Renamed))
            convert filename lflag stx
          "'" -> do
            stx <- parser :: P (N (note Raw) (stx Raw))
            convert' filename stx
          _        -> do
            stx <- parser :: P (N (note Raw) (stx Raw))
            convert filename lflag stx
  convert filename flag stx =
    return . maybe toAstQ toLocAstQ flag $
               scrubWhen (\loc -> file loc == filename) stx
  convert' filename stx = do
    return . toAstQ' $ scrubWhen (\loc -> file loc == filename) stx

deriveLocAsts 'toAstQ syntaxTable

