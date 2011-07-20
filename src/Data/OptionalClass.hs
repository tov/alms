-- | A generalization of 'Maybe'
module Data.OptionalClass (
  Optional(..),
  coerceOpt, catOpt, fromOptSome, fromOpt,
  isOptSome, isOptNone,
  mapOpt,
) where

class Functor f ⇒ Optional f where
  foldOpt ∷ b → (a → b) → f a → b
  optSome ∷ a → f a
  optNone ∷ f a

instance Optional Maybe where
  foldOpt = maybe
  optSome = Just
  optNone = Nothing

instance Optional [] where
  foldOpt z f = foldr (const . f) z
  optSome     = return
  optNone     = []

-- | Coerce between optional types
coerceOpt ∷ (Optional f, Optional g) ⇒ f a → g a
coerceOpt  = foldOpt optNone optSome

catOpt ∷ Optional f ⇒ [f a] → [a]
catOpt = foldr (foldOpt id (:)) []

fromOptSome ∷ Optional f ⇒ f a → a
fromOptSome = foldOpt (error "fromOptSome: got optNone") id

fromOpt ∷ Optional f ⇒ a → f a → a
fromOpt = flip foldOpt id

isOptSome, isOptNone ∷ Optional f ⇒ f a → Bool
isOptSome = foldOpt False (const True)
isOptNone = not . isOptSome

mapOpt ∷ Optional f ⇒ (a → f b) → [a] → [b]
mapOpt f = foldr (foldOpt id (:) . f) []

