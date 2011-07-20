-- | Pretty printing of internal types
module Type.Ppr ( TyConInfo(..) ) where

import Util
import qualified AST
import Type.Internal
import Type.Syntax
import Type.TyVar
import Type.ArrowAnnotations
import Syntax.Ppr

import Prelude ()
import qualified Data.Set as S

instance Tv tv ⇒ Ppr (Type tv) where
  ppr τ = askTyNames $ \tn → ppr (typeToStx t2sContext0 { t2sTyNames = tn } τ)

instance Ppr TyPat where
  ppr tp = askTyNames $ \tn → ppr (fst (tyPatToStx tn [] tp))

instance Ppr TyCon where
  ppr tc = askTyNames $ \tn → ppr (tyConToStx tn tc)

instance Tv tv ⇒ Ppr (QExp tv) where
  ppr QeA        = char 'A'
  ppr (QeU αset) = case S.toList αset of
    []  → char 'U'
    [α] → ppr α
    αs  → prec precTySemi $
            fcat (punctuate (char '⋁') (ppr0 <$> αs))

instance Ppr TyConVariety where
  ppr AbstractType = text "abstract type"
  ppr DataType     = text "data type"
  ppr OperatorType = text "type synonym or operator"

instance Tv tv ⇒ Show (Type tv) where showsPrec = showFromPpr
instance Show TyPat where showsPrec = showFromPpr
instance Show TyCon where showsPrec = showFromPpr
instance Tv tv ⇒ Show (QExp tv) where showsPrec = showFromPpr
instance Show TyConVariety where showsPrec = showFromPpr

-- | For verbose printing of 'TyCon's
newtype TyConInfo = TyConInfo TyCon

instance Ppr TyConInfo where
  ppr (TyConInfo tc) | tc == tcExn = text "exn"
  ppr (TyConInfo tc) = askTyNames $ \tn → atPrec 0 $
    case view (tyConToStx tn tc) of
      AST.TdSyn { AST.tdClauses = [(tps, t)] } →
        pprTyApp (tcName tc) (ps (snd <$> tvs))
          >?> qe (fst <$> tvs)
            >?> char '=' <+> ppr t
          where
            tvs = [ case view tp of
                      AST.TpVar tv _ → (tv, ppr tv)
                      _              →
                        let tv  = AST.TV (AST.ident (show i)) qlit bogus
                            tv' = case qlit of
                                    Qa → ppr tv <> char '=' <>
                                          mapPrec (max precEq) (ppr tp)
                                    Qu → ppr tp
                         in (tv, tv')
                  | tp   ← tps
                  | qlit ← tcBounds tc
                  | i    ← [ 1 ∷ Int .. ] ]
      AST.TdSyn { AST.tdClauses = next } →
        pprTyApp (tcName tc) (ps tvs)
          >?> (qe tvs <+> text "with"
          $$ vcat (map alt next))
            where
              tvs  = [ AST.TV (AST.ident (show i)) qlit bogus
                     | qlit ← tcBounds tc
                     | i ← [ 1 .. ] ∷ [Int] ]
              alt (tps,t) = char '|' <+> pprPrec precApp tps
                              <+> ppr (AST.jname (tcName tc))
                              >?> char '=' <+> ppr t
      AST.TdAbs { AST.tdParams = tvs } →
        pprTyApp (tcName tc) (ps tvs)
          >?> qe tvs
      AST.TdDat { AST.tdParams = tvs, AST.tdAlts = altsList } →
        pprTyApp (tcName tc) (ps tvs)
          >?> qe tvs
            >?> alts
        where
          alts = sep $
                 mapHead (text "=" <+>) $
                 mapTail (text "|" <+>) $
                 map alt altsList
          alt (u, Nothing) = ppr u
          alt (u, Just t)  = ppr u <+> text "of" <+> ppr t
      AST.TdAnti a → AST.antierror "ppr (TyConInfo)" a
    where
      qe tvs = case tcQual tc of
                 QeU αs | S.null αs
                     → mempty
                 qe' → colon <+> ppr (qRepresent (tvs !!) qe')
      ps tvs = [ ppr var <> pprPrec (precApp + 1) tv
               | tv  ← tvs
               | var ← tcArity tc ]
