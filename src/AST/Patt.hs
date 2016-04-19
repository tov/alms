module AST.Patt (
  -- * Patterns
  Patt'(..), Patt, PattNote(..), newPatt,
  -- ** Constructors
  paWild, paVar, paCon, paPair, paLit, paAs, paInj, paAnn,
  paBang, paRec, paAnti,
  -- ** Synthetic pattern constructors
  paChar, paStr, paInt, paFloat, paUnit, paCons, paNil,
  ToPatt(..),
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
  -- | record pattern
  | PaRec (Uid i) (Patt i) (Patt i)
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
  PaRec _ x y      ->
    newNote {
      pdv_    = dv x `mappend` dv y
    }
  PaBang x         ->
    newNote {
      pdv_    = dv x
    }
  PaAnti a         ->
    newNote {
      pdv_    = antierror "dv" a
    }

instance Dv (N (PattNote i) a) i where
  dv = pdv_ . noteOf

deriveNotable 'newPatt (''Tag, [0]) ''Patt

paChar :: Tag i => Char -> Patt i
paChar = paLit . LtChar

paStr :: Tag i => String -> Patt i
paStr  = paLit . LtStr

paInt :: (Tag i, Integral a) => a -> Patt i
paInt  = paLit . LtInt . toInteger

paFloat :: Tag i => Double -> Patt i
paFloat  = paLit . LtFloat

paUnit :: Tag i => Patt i
paUnit  = paCon idUnitVal Nothing

paCons :: Tag i => Patt i -> Patt i -> Patt i
paCons  = paCon idConsList . Just <$$> paPair

paNil  :: Tag i => Patt i
paNil   = paCon idNilList Nothing

class ToPatt a i where
  toPatt ∷ a → Patt i

instance ToPatt (Patt i) i where
  toPatt = id

instance Tag i ⇒ ToPatt (VarId i) i where
  toPatt = paVar

instance (Tag i, ToPatt a i, ToPatt b i) ⇒ ToPatt (a, b) i where
  toPatt (a, b) = paPair (toPatt a) (toPatt b)

instance Tag i ⇒ ToPatt String i where
  toPatt = paStr

instance Tag i ⇒ ToPatt Int i where
  toPatt = paInt

instance Tag i ⇒ ToPatt Char i where
  toPatt = paChar

instance Tag i ⇒ ToPatt Double i where
  toPatt = paFloat

