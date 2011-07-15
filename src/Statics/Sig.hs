{-# LANGUAGE
      DeriveDataTypeable,
      DeriveFunctor,
      UnicodeSyntax
    #-}
module Statics.Sig (
  Signature, SigItem (..),
  sigToStx, sigToStx', sigItemToStx, sigItemToStx',
) where

import Util
import qualified AST
import AST.Ident
import Type
import qualified Syntax.Ppr as Ppr

import Prelude ()
import Data.Generics (Typeable, Data)

type R = Renamed

data SigItem tv
  = SiValue   !(Lid R) !(Type tv)
  | SiType    !(Lid R) !TyCon
  | SiExn     !(Uid R) !(Maybe (Type tv))
  | SiModule  !(Uid R) !(Signature tv)
  | SiModType !(Uid R) !(Signature tv)
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
  SiValue n τ     → AST.sgVal n (typeToStx t2sc τ)
  SiType _ tc     → AST.sgTyp [tyConToStx tn tc]
  SiExn n mτ      → AST.sgExn n (typeToStx t2sc <$> mτ)
  SiModule n sig  → AST.sgMod n (sigToStx (tnEnter tn n) sig)
  SiModType n sig → AST.sgSig n (sigToStx tn sig)
  where
  t2sc = t2sContext0 { t2sTyNames = tn }

instance Tv tv ⇒ Ppr.Ppr (SigItem tv) where
  ppr item = Ppr.askTyNames $ \tn → Ppr.ppr (sigItemToStx tn item)
  pprList sig = Ppr.askTyNames $ \tn → Ppr.ppr (sigToStx tn sig)

instance Tv tv ⇒ Show (SigItem tv) where
  showsPrec = Ppr.showFromPpr
  showList  = Ppr.showFromPpr 0
