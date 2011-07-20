module AST.Patt (
  -- * Patterns
  Patt'(..), Patt, PattNote(..), newPatt,
  -- ** Constructors
  paWild, paVar, paCon, paPair, paLit, paAs, paInj, paAnn, paBang, paAnti,
) where

import Util
import Meta.DeriveNotable
import AST.Notable
import AST.Anti
import AST.Ident
import AST.Lit
import AST.Type

import Prelude ()
import Data.Generics (Typeable, Data)

type Patt i = N (PattNote i) (Patt' i)

-- | Patterns
data Patt' i
  -- | wildcard
  = PaWild
  -- | variable pattern
  | PaVar (VarId i)
  -- | datacon, possibly with parameter, possibly an exception
  | PaCon (QConId i) (Maybe (Patt i))
  -- | pair pattern
  | PaPair (Patt i) (Patt i)
  -- | literal pattern
  | PaLit Lit
  -- | bind an identifer and a pattern (@as@)
  | PaAs (Patt i) (VarId i)
  -- | open variant
  | PaInj (Uid i) (Maybe (Patt i))
  -- | type annotation on a pattern
  | PaAnn (Patt i) (Type i)
  -- | imperative/threaded binding
  | PaBang (Patt i)
  -- | antiquote
  | PaAnti Anti
  deriving (Typeable, Data)

data PattNote i
  = PattNote {
      -- | source location
      ploc_  :: !Loc,
      -- | defined variables
      pdv_   :: [VarId i]
    }
  deriving (Typeable, Data)

instance Locatable (PattNote i) where
  getLoc = ploc_

instance Relocatable (PattNote i) where
  setLoc note loc = note { ploc_ = loc }

instance Notable (PattNote i) where
  newNote = PattNote bogus mempty

newPatt :: Tag i => Patt' i -> Patt i
newPatt p0 = flip N p0 $ case p0 of
  PaWild           ->
    newNote {
      pdv_    = mempty
    }
  PaVar x          ->
    newNote {
      pdv_    = [x]
    }
  PaCon _ mx       ->
    newNote {
      pdv_    = maybe mempty dv mx
    }
  PaPair x y       ->
    newNote {
      pdv_    = dv x `mappend` dv y
    }
  PaLit _          ->
    newNote {
      pdv_    = mempty
    }
  PaAs x y         ->
    newNote {
      pdv_    = dv x ++ [y]
    }
  PaInj _ my       ->
    newNote {
      pdv_    = maybe mempty dv my
    }
  PaAnn x _        ->
    newNote {
      pdv_    = dv x
    }
  PaBang x         ->
    newNote {
      pdv_    = dv x
    }
  PaAnti a         ->
    newNote {
      pdv_    = antierror "dv" a
    }

instance Tag i => Dv (N (PattNote i) a) i where
  dv = pdv_ . noteOf

deriveNotable 'newPatt (''Tag, [0]) ''Patt

