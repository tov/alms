{-# LANGUAGE
      UnicodeSyntax
    #-}
-- | Pretty printing of internal types
module Type.Ppr ( ) where

import Util
import Type.Internal
import Type.Syntax
import Type.TyVar
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

instance Tv tv ⇒ Show (Type tv) where showsPrec = showFromPpr
instance Show TyPat where showsPrec = showFromPpr
instance Show TyCon where showsPrec = showFromPpr
instance Tv tv ⇒ Show (QExp tv) where showsPrec = showFromPpr

