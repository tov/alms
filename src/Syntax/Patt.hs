{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      NoMonomorphismRestriction,
      TemplateHaskell,
      TypeFamilies,
      TypeSynonymInstances #-}
module Syntax.Patt (
  Patt'(..), Patt, PattNote(..), newPatt,
  paWild, paVar, paCon, paPair, paLit, paAs, paPack, paAnti,
  dtv
) where

import Meta.DeriveNotable
import Syntax.Notable
import Syntax.Anti
import Syntax.Ident
import Syntax.Lit

import qualified Data.Set as S
import Data.Generics (Typeable, Data)

type Patt i = N (PattNote i) (Patt' i)

-- | Patterns
data Patt' i
  -- | wildcard
  = PaWild
  -- | variable pattern
  | PaVar (Lid i)
  -- | datacon, possibly with parameter, possibly an exception
  | PaCon (QUid i) (Maybe (Patt i))
  -- | pair pattern
  | PaPair (Patt i) (Patt i)
  -- | literal pattern
  | PaLit Lit
  -- | bind an identifer and a pattern (@as@)
  | PaAs (Patt i) (Lid i)
  -- | existential opening
  | PaPack (TyVar i) (Patt i)
  -- | antiquote
  | PaAnti Anti
  deriving (Typeable, Data)

data PattNote i
  = PattNote {
      -- | source location
      ploc_  :: !Loc,
      -- | defined variables
      pdv_   :: S.Set (Lid i),
      -- | defined type variables
      pdtv_  :: S.Set (TyVar i)
    }
  deriving (Typeable, Data)

instance Locatable (PattNote i) where
  getLoc = ploc_

instance Relocatable (PattNote i) where
  setLoc note loc = note { ploc_ = loc }

instance Notable (PattNote i) where
  newNote = PattNote bogus S.empty S.empty

newPatt :: Id i => Patt' i -> Patt i
newPatt p0 = flip N p0 $ case p0 of
  PaWild           ->
    newNote {
      pdv_    = S.empty,
      pdtv_   = S.empty
    }
  PaVar x          ->
    newNote {
      pdv_    = S.singleton x,
      pdtv_   = S.empty
    }
  PaCon _ Nothing  ->
    newNote {
      pdv_    = S.empty,
      pdtv_   = S.empty
    }
  PaCon _ (Just x) ->
    newNote {
      pdv_    = dv x,
      pdtv_   = dtv x
    }
  PaPair x y       ->
    newNote {
      pdv_    = dv x `S.union` dv y,
      pdtv_   = dtv x `S.union` dtv y
    }
  PaLit _          ->
    newNote {
      pdv_    = S.empty,
      pdtv_   = S.empty
    }
  PaAs x y         ->
    newNote {
      pdv_    = S.insert y (dv x),
      pdtv_   = dtv x
    }
  PaPack tv x       ->
    newNote {
      pdv_    = dv x,
      pdtv_   = S.insert tv (dtv x)
    }
  PaAnti a         ->
    newNote {
      pdv_    = antierror "dv" a,
      pdtv_   = antierror "dtv" a
    }

instance Id i => Dv (N (PattNote i) a) i where
  dv = pdv_ . noteOf

dtv :: Id i => Patt i -> S.Set (TyVar i)
dtv = pdtv_ . noteOf

deriveNotable 'newPatt (''Id, [0]) ''Patt

