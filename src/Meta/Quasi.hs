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
toAstQ x = whichS' (toExpQ x) (toPatQ x)

toExpQ :: Data a => a -> TH.ExpQ
toExpQ  = dataToExpQ antiExp moduleQuals

toPatQ :: Data a => a -> TH.PatQ
toPatQ  = dataToPatQ antiPat moduleQuals

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

ex  = mkQuasi parseExpr
dc  = mkQuasi parseDecl
ty  = mkQuasi parseType
me  = mkQuasi parseModExp
pa  = mkQuasi parsePatt
prQ = mkQuasi parseProg
tdQ = mkQuasi parseTyDec
atQ = mkQuasi parseAbsTy
caQ = mkQuasi parseCaseAlt
bnQ = mkQuasi parseBinding
qeQ = mkQuasi parseQExp
tpQ = mkQuasi parseTyPat
seQ = mkQuasi parseSigExp
sgQ = mkQuasi parseSigItem

mkQuasi :: forall stx note.
           (Data (note Raw), Data (stx Raw),
            LocAst (N (note Raw) (stx Raw)),
            Data (note Renamed), Data (stx Renamed),
            LocAst (N (note Renamed) (stx Renamed))) =>
           (forall i. Id i => P (N (note i) (stx i))) ->
           QuasiQuoter
mkQuasi parser = QuasiQuoter qast qast where
  qast s =
    join $
      parseQuasi s $ \iflag lflag ->
        case iflag of
          Just '+' -> do
            stx <- parser :: P (N (note Renamed) (stx Renamed))
            convert lflag stx
          _        -> do
            stx <- parser :: P (N (note Raw) (stx Raw))
            convert lflag stx
  convert flag stx = return $ maybe toAstQ toLocAstQ flag (scrub stx)

deriveLocAsts 'toAstQ syntaxTable

