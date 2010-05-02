{-# LANGUAGE
      DeriveDataTypeable,
      TemplateHaskell #-}
module Syntax.Patt (
  Patt(..), pv, ptv
) where

import Syntax.Anti
import Syntax.Ident
import Syntax.Lit

import qualified Data.Set as S
import Data.Generics (Typeable, Data, everything, mkQ)

-- | Patterns
data Patt
  -- | wildcard
  = PaWild
  -- | variable pattern
  | PaVar Lid
  -- | datacon, possibly with parameter, possibly an exception
  | PaCon QUid (Maybe Patt) Bool
  -- | pair pattern
  | PaPair Patt Patt
  -- | literal pattern
  | PaLit Lit
  -- | bind an identifer and a pattern (@as@)
  | PaAs Patt Lid
  -- | existential opening
  | PaPack TyVar Patt
  -- | antiquote
  | PaAnti Anti
  deriving (Typeable, Data)

-- | The set of variables bound by a pattern
pv :: Patt -> S.Set Lid
pv PaWild               = S.empty
pv (PaVar x)            = S.singleton x
pv (PaCon _ Nothing _)  = S.empty
pv (PaCon _ (Just x) _) = pv x
pv (PaPair x y)         = pv x `S.union` pv y
pv (PaLit _)            = S.empty
pv (PaAs x y)           = pv x `S.union` S.singleton y
pv (PaPack _ x)         = pv x
pv (PaAnti a)           = antierror "pv" a

ptv :: Patt -> S.Set TyVar
ptv = everything S.union $ mkQ S.empty S.singleton
