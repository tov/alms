{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      NoMonomorphismRestriction,
      TemplateHaskell,
      TypeFamilies,
      TypeSynonymInstances #-}
module Syntax.Patt (
  Patt'(..), Patt,
  paWild, paVar, paCon, paPair, paLit, paAs, paPack, paAnti,
  ptv
) where

import Meta.DeriveNotable
import Syntax.Notable
import Syntax.Anti
import Syntax.Ident
import Syntax.Lit

import qualified Data.Set as S
import Data.Generics (Typeable, Data, everything, mkQ)

-- | Patterns
data Patt' i
  -- | wildcard
  = PaWild
  -- | variable pattern
  | PaVar (Lid i)
  -- | datacon, possibly with parameter, possibly an exception
  | PaCon (QUid i) (Maybe (Patt i)) Bool
  -- | pair pattern
  | PaPair (Patt i) (Patt i)
  -- | literal pattern
  | PaLit Lit
  -- | bind an identifer and a pattern (@as@)
  | PaAs (Patt i) (Lid i)
  -- | existential opening
  | PaPack TyVar (Patt i)
  -- | antiquote
  | PaAnti Anti
  deriving (Typeable, Data)

type Patt i = Located Patt' i

deriveNotable ''Patt

instance Id i => Dv (Patt' i) i where
  dv PaWild               = S.empty
  dv (PaVar x)            = S.singleton x
  dv (PaCon _ Nothing _)  = S.empty
  dv (PaCon _ (Just x) _) = dv x
  dv (PaPair x y)         = dv x `S.union` dv y
  dv (PaLit _)            = S.empty
  dv (PaAs x y)           = dv x `S.union` S.singleton y
  dv (PaPack _ x)         = dv x
  dv (PaAnti a)           = antierror "dv" a

instance Id i => Dv (N note (Patt' i)) i where
  dv = dv . dataOf

ptv :: Id i => Patt i -> S.Set TyVar
ptv = everything S.union $ mkQ S.empty S.singleton
