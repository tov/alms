-- | An uninhabited type
module Data.Empty (
  Empty, elimEmpty, elimEmptyF,
) where

import Data.Generics (Typeable, Data(..), mkDataType)
import Unsafe.Coerce (unsafeCoerce)

-- | An uninhabited type
data Empty deriving Typeable

instance Data Empty where
  gfoldl _ _    = elimEmpty
  gunfold _ _ _ = error "Empty.gunfold"
  toConstr      = elimEmpty
  dataTypeOf _  = mkDataType "Data.Empty" []

-- | Elimination for 'Empty'
elimEmpty  ∷ Empty → a
elimEmpty  = const (error "elimEmpty")

-- | Elimination for 'Empty' under any functor, implemented as a no-op.
elimEmptyF ∷ Functor f ⇒ f Empty → f a
elimEmptyF = unsafeCoerce

instance Eq Empty where _ == _ = True
instance Ord Empty where _ `compare` _ = EQ
instance Show Empty where show = elimEmpty

