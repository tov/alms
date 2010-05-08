module Syntax.POClass (
  -- * Partial orders
  PO(..), bigVee, bigVeeM, bigWedge, bigWedgeM,
) where

import Util

import qualified Data.Set as S

-- | Partial orders.
--  Minimal complete definition is one of:
--
--  * 'ifMJ'
--
--  * '\/', '/\'    (only if it's a lattice)
--
--  * '\/?', '/\?'  (partial join and meet)
class Eq a => PO a where
  -- | Takes a boolean parameter, and does join if true
  --   and meet if false.  This sometimes allows us to exploit duality
  --   to define both at once.
  ifMJ :: Monad m => Bool -> a -> a -> m a
  ifMJ True  x y = return (x \/ y)
  ifMJ False x y = return (x /\ y)

  -- | Partial join returns in a monad, in case join DNE
  (\/?) :: Monad m => a -> a -> m a
  (\/?)  = ifMJ True

  -- | Partial meet returns in a monad, in case meet DNE
  (/\?) :: Monad m => a -> a -> m a
  (/\?)  = ifMJ False

  -- | Total join
  (\/)  :: a -> a -> a
  -- | Total meet
  (/\)  :: a -> a -> a
  x \/ y = fromJust (x \/? y)
  x /\ y = fromJust (x /\? y)

  -- | The order relation (derived)
  (<:)  :: a -> a -> Bool
  x <: y = Just x == (x /\? y)
        || Just y == (x \/? y)

  -- | The complement of the order relation (derived)
  (/<:) :: a -> a -> Bool
  (/<:) = not <$$> (<:)

infixl 7 /\, /\?
infixl 6 \/, \/?
infix 4 <:

bigVee :: (Bounded a, PO a) => [a] -> a
bigVee  = foldr (\/) minBound

bigVeeM :: (Monad m, Bounded a, PO a) => [a] -> m a
bigVeeM  = foldrM (\/?) minBound

bigWedge :: (Bounded a, PO a) => [a] -> a
bigWedge  = foldr (/\) maxBound

bigWedgeM :: (Monad m, Bounded a, PO a) => [a] -> m a
bigWedgeM  = foldrM (/\?) maxBound

instance Ord a => PO (S.Set a) where
  (\/) = S.union
  (/\) = S.intersection

