-- | An uninhabited type
module Data.Empty (
  Empty, elimEmpty, elimEmptyF,
) where

import Data.Generics (Typeable, Data)
import Unsafe.Coerce (unsafeCoerce)

-- | An uninhabited type
data Empty deriving Typeable

deriving instance Data Empty

-- | Elimination for 'Empty'
elimEmpty  ∷ Empty → a
elimEmpty  = const undefined

-- | Elimination for 'Empty' under any functor, implemented as a no-op.
elimEmptyF ∷ Functor f ⇒ f Empty → f a
elimEmptyF = unsafeCoerce

instance Eq Empty where _ == _ = True
instance Ord Empty where _ `compare` _ = EQ
instance Show Empty where show = elimEmpty

