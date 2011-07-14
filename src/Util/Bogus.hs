{-# LANGUAGE
      UnicodeSyntax
    #-}
-- | Interface for producing bogus results, usually when an error
--   has occurred but we want to keep going to try to find more errors.
module Util.Bogus (
  Bogus(..), IsBogus(..),
) where

-- | A bogus value.
class Bogus a where
  bogus ∷ a

-- | Test for bogosity.
class Bogus a ⇒ IsBogus a where
  isBogus ∷ a → Bool

instance Bogus () where
  bogus = ()

instance Bogus (Maybe a) where
  bogus = Nothing

instance Bogus [a] where
  bogus = []

instance Bogus a ⇒ Bogus (Either a b) where
  bogus = Left bogus

instance IsBogus a ⇒ IsBogus (Either a b) where
  isBogus = either isBogus (const False)

instance (Bogus a, Bogus b) ⇒ Bogus (a, b) where
  bogus = (bogus, bogus)

instance (IsBogus a, IsBogus b) ⇒ IsBogus (a, b) where
  isBogus (a, b) = isBogus a && isBogus b

instance (Bogus a, Bogus b, Bogus c) ⇒ Bogus (a, b, c) where
  bogus = (bogus, bogus, bogus)

instance (IsBogus a, IsBogus b, IsBogus c) ⇒ IsBogus (a, b, c) where
  isBogus (a, b, c) = isBogus a && isBogus b && isBogus c

