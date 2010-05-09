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
data Patt i
  -- | wildcard
  = PaWild
  -- | variable pattern
  | PaVar Lid
  -- | datacon, possibly with parameter, possibly an exception
  | PaCon QUid (Maybe (Patt i)) Bool
  -- | pair pattern
  | PaPair (Patt i) (Patt i)
  -- | literal pattern
  | PaLit Lit
  -- | bind an identifer and a pattern (@as@)
  | PaAs (Patt i) Lid
  -- | existential opening
  | PaPack TyVar (Patt i)
  -- | antiquote
  | PaAnti Anti
  deriving (Typeable, Data)

-- | The set of variables bound by a pattern
pv :: Patt i -> S.Set Lid
pv PaWild               = S.empty
pv (PaVar x)            = S.singleton x
pv (PaCon _ Nothing _)  = S.empty
pv (PaCon _ (Just x) _) = pv x
pv (PaPair x y)         = pv x `S.union` pv y
pv (PaLit _)            = S.empty
pv (PaAs x y)           = pv x `S.union` S.singleton y
pv (PaPack _ x)         = pv x
pv (PaAnti a)           = antierror "pv" a

ptv :: Id i => Patt i -> S.Set TyVar
ptv = everything S.union $ mkQ S.empty S.singleton
