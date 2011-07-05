{-# LANGUAGE
      DeriveFunctor,
      UnicodeSyntax
  #-}
-- | Like maybe, but 'Eq' and 'Ord' instances are collapsed so that all
--   values of type @Perhaps a@ are equal. Useful for hiding optional
--   information from derived instances in other datatypes.
module Data.Perhaps (
  Perhaps(..),
  catPerhaps, mapPerhaps,
  fromHere, fromPerhaps, isHere, isNope,
  listToPerhaps, perhapsToList, perhapsToMaybe, maybeToPerhaps,
) where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Fix
import Data.Monoid

import Data.OptionalClass

-- | This is like @Maybe@, except all values of the type compare as
--   equal, which is useful for “suggestions” in the syntax that have
--   no semantic significance.
data Perhaps a
  = Nope
  | Here a
  deriving Functor

instance Optional Perhaps where
  foldOpt = perhaps
  optSome = Here
  optNone = Nope

perhaps ∷ b → (a → b) → Perhaps a → b
perhaps nope _    Nope     = nope
perhaps _    here (Here x) = here x

catPerhaps ∷ [Perhaps a] → [a]
catPerhaps = foldr (perhaps id (:)) []

fromHere ∷ Perhaps a → a
fromHere = perhaps (error "fromHere: got Nope") id

fromPerhaps ∷ a → Perhaps a → a
fromPerhaps = flip perhaps id

isHere, isNope ∷ Perhaps a → Bool
isHere = perhaps False (const True)
isNope = not . isHere

listToPerhaps ∷ [a] → Perhaps a
listToPerhaps = foldr (const . Here) Nope

mapPerhaps ∷ (a → Perhaps b) → [a] → [b]
mapPerhaps f = foldr (perhaps id (:) . f) []

perhapsToList ∷ Perhaps a → [a]
perhapsToList = perhaps [] (:[])

perhapsToMaybe ∷ Perhaps a → Maybe a
perhapsToMaybe = perhaps Nothing Just

maybeToPerhaps ∷ Maybe a → Perhaps a
maybeToPerhaps = maybe Nope Here

instance Eq (Perhaps a) where
  _ == _ = True

instance Monad Perhaps where
  return = Here
  (>>=)  = perhaps (const Nope) (flip ($))

instance Ord (Perhaps a) where
  _ `compare` _ = EQ

instance Read a ⇒ Read (Perhaps a) where
  readsPrec p s = case readsPrec p s of
    [] → [ (Nope, s) ]
    xs → map (first Here) xs

instance Show a ⇒ Show (Perhaps a) where
  showsPrec = perhaps id . showsPrec

instance MonadFix Perhaps where
  mfix f = let a = f (unHere a) in a
     where unHere (Here x) = x
           unHere Nope     = error "mfix Perhaps: Nope"

instance MonadPlus Perhaps where
  mzero = Nope
  mplus = perhaps id (const . Here)

instance Applicative Perhaps where
  pure  = return
  (<*>) = ap

instance Monoid a ⇒ Monoid (Perhaps a) where
  mempty  = Nope
  Here x1 `mappend` Here x2 = Here (x1 `mappend` x2)
  p1      `mappend` Nope    = p1
  Nope    `mappend` p2      = p2

instance Alternative Perhaps where
  empty  = mzero
  (<|>)  = mplus

