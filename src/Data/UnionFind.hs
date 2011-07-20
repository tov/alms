{- | Based on Simonet's Dalton constraint solver -}
module Data.UnionFind (
  -- * An implementation on top of 'MonadRef'
  Proxy,
  create, desc, setDesc, repr,
  sameRepr, isRepr, coalesce, coalesce_, linkto,
) where

import Util
import Util.Eq1
import Util.MonadRef

import Prelude ()

---
--- Representaiton and basic, low-level operations
---

newtype Proxy p a = Proxy { unProxy ∷ p (Either a (Proxy p a)) }

instance Eq1 p ⇒ Eq1 (Proxy p) where
  Proxy p1 `eq1` Proxy p2 = p1 `eq1` p2

-- | To create a new set with the given representative
create  ∷ MonadRef p m ⇒ a → m (Proxy p a)
create   = liftM Proxy . newRef . Left

-- | To follow a link, either to the end or to another link
follow  ∷ MonadRef p m ⇒ Proxy p a → m (Either a (Proxy p a))
follow   = readRef . unProxy

-- | To replace the contents of a link with a representative
--   or another link
replace ∷ MonadRef p m ⇒ Proxy p a → Either a (Proxy p a) → m ()
replace  = writeRef . unProxy

-- | Find the representative of a set
repr    ∷ MonadRef p m ⇒ Proxy p a → m (Proxy p a)
repr    = liftM fst . loop where
  loop proxy = do
    link ← follow proxy
    case link of
      Left _       → return (proxy, False)
      Right proxy' → do
        (proxy'', changed) ← loop proxy'
        when changed $ replace proxy (Right proxy'')
        return (proxy'', True)

-- | Find the descriptor of a set
desc     ∷ MonadRef p m ⇒ Proxy p a → m a
desc proxy = do
  link ← follow proxy
  case link of
    Left a       → return a
    Right proxy' → desc =<< repr proxy'

-- | Change the descriptor of a set
setDesc ∷ MonadRef p m ⇒ Proxy p a → a → m ()
setDesc proxy a = flip replace (Left a) =<< repr proxy

-- | Join two proxies, using the given function to combine their
--   descriptors.
coalesce ∷ MonadRef p m ⇒
           (a → a → m (a, b)) → Proxy p a → Proxy p a → m (Maybe b)
coalesce combine proxy1 proxy2 = do
  proxy1' ← repr proxy1
  proxy2' ← repr proxy2
  if (proxy1' `eq1` proxy2')
    then return Nothing
    else do
      a1      ← desc proxy1'
      a2      ← desc proxy2'
      (a', b) ← combine a1 a2
      replace proxy1' (Right proxy2')
      replace proxy2' (Left a')
      return (Just b)

coalesce_ ∷ MonadRef p m ⇒ (a → a → m a) → Proxy p a → Proxy p a → m ()
coalesce_ combine proxy1 proxy2 = do
  coalesce (liftM (,()) <$$> combine) proxy1 proxy2
  return ()

-- | Make the first proxy point to the second, keeping the second
--   proxy's descriptor
linkto ∷ MonadRef p m ⇒ Proxy p a → Proxy p a → m ()
linkto = coalesce_ (const . return)

-- | Is the given proxy object the representative of its set?
isRepr ∷ MonadRef p m ⇒ Proxy p a → m Bool
isRepr = liftM (either (const True) (const False)) . follow

-- | Are two proxy objects from the same set?
sameRepr ∷ MonadRef p m ⇒ Proxy p a → Proxy p a → m Bool
sameRepr proxy1 proxy2 = liftM2 eq1 (repr proxy1) (repr proxy2)

