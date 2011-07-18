{-# LANGUAGE
      DeriveDataTypeable,
      DeriveFunctor,
      UnicodeSyntax
    #-}
module Statics.Sig (
  Signature, SigItem (..),
  sigToStx, sigToStx', sigItemToStx, sigItemToStx',
  VarId, ModId, SigId, QVarId, QModId, QSigId,
) where

import Util
import qualified AST
import Type
import qualified Syntax.Ppr as Ppr

import Prelude ()
import Data.Generics (Typeable, Data)

type R = AST.Renamed
type VarId  = AST.VarId R
type ModId  = AST.ModId R
type SigId  = AST.SigId R
type QVarId = AST.VarId R
type QModId = AST.ModId R
type QSigId = AST.SigId R

data SigItem tv
  = SgVal !VarId !(Type tv)
  | SgTyp !TypId !TyCon
  | SgExn !ConId !(Maybe (Type Empty))
  | SgMod !ModId !(Signature tv)
  | SgSig !SigId !(Signature tv)
  deriving (Functor, Typeable, Data)

type Signature tv = [SigItem tv]

-- | Convert an internal signature to AST, with no type context
sigToStx' ∷ Tv tv ⇒ Signature tv → AST.SigExp R
sigToStx' = sigToStx tyNames0

-- | Convert an internal signature to AST
sigToStx ∷ Tv tv ⇒ TyNames → Signature tv → AST.SigExp R
sigToStx tn items = AST.seSig (sigItemToStx tn <$> items)

-- | Convert an internal signature item to an AST signature item,
--   with no type context.
sigItemToStx' ∷ Tv tv ⇒ SigItem tv → AST.SigItem R
sigItemToStx' = sigItemToStx tyNames0

-- | Convert an internal signature item to an AST signature item
--   TODO: Group mutually recursive types.
sigItemToStx ∷ Tv tv ⇒ TyNames → SigItem tv → AST.SigItem R
sigItemToStx tn si0 = case si0 of
  SgVal n τ   → AST.sgVal n (typeToStx t2sc τ)
  SgTyp _ tc  → AST.sgTyp [tyConToStx tn tc]
  SgExn n mτ  → AST.sgExn n (typeToStx t2sc <$> mτ)
  SgMod n sig → AST.sgMod n (sigToStx (tnEnter tn n) sig)
  SgSig n sig → AST.sgSig n (sigToStx tn sig)
  where
  t2sc = t2sContext0 { t2sTyNames = tn }

instance Tv tv ⇒ Ppr.Ppr (SigItem tv) where
  ppr item = Ppr.askTyNames $ \tn → Ppr.ppr (sigItemToStx tn item)
  pprList sig = Ppr.askTyNames $ \tn → Ppr.ppr (sigToStx tn sig)

instance Tv tv ⇒ Show (SigItem tv) where
  showsPrec = Ppr.showFromPpr
  showList  = Ppr.showFromPpr 0
