-- | A generalization of @Data.Graph.Inductive.NodeMap@ from the fgs package
module Alt.NodeMap (
  MonadNM(..),
  module Data.Graph.Inductive.NodeMap,
) where

import Data.Graph.Inductive (DynGraph, LNode, LEdge, insNode, lab)
import Data.Graph.Inductive.NodeMap
  hiding (mkNodeM, mkNodesM, mkEdgeM, mkEdgesM,
          insMapNodeM, insMapEdgeM, delMapNodeM, delMapEdgeM,
          insMapNodesM, insMapEdgesM, delMapNodesM, delMapEdgesM)
import Control.Monad.State.Lazy as Lazy
import Control.Monad.State.Strict as Strict
import Control.Monad.Reader
import Control.Monad.Writer.Lazy as Lazy
import Control.Monad.Writer.Strict as Strict
import Control.Monad.RWS.Lazy as Lazy
import Control.Monad.RWS.Strict as Strict
import Control.Arrow

insNewMapNode ∷ (Ord a, DynGraph gr) ⇒
                NodeMap a → a → gr a b → (gr a b, NodeMap a, LNode a)
insNewMapNode nm a gr = (gr', nm', node) where
  (node@(n, _), nm') = mkNode nm a
  gr'                = maybe (insNode node gr) (const gr) (lab gr n)

insNewMapNodes ∷ (Ord a, DynGraph gr) ⇒
                 NodeMap a → [a] → gr a b → (gr a b, NodeMap a, [LNode a])
insNewMapNodes nm []     gr = (gr, nm, [])
insNewMapNodes nm (a:as) gr = (gr'', nm'', node:nodes) where
  (gr',  nm',  node)  = insNewMapNode nm a gr
  (gr'', nm'', nodes) = insNewMapNodes nm' as gr'

class (Ord a, DynGraph g, Monad m) ⇒
      MonadNM a b g m | m → a b g where
  putNMState    ∷ (NodeMap a, g a b) → m ()
  putNodeMap    ∷ NodeMap a → m ()
  putGraph      ∷ g a b → m ()
  getNMState    ∷ m (NodeMap a, g a b)
  getNodeMap    ∷ m (NodeMap a)
  getGraph      ∷ m (g a b)
  --
  modifyNMState ∷ ((NodeMap a, g a b) → (NodeMap a, g a b)) → m ()
  modifyNodeMap ∷ (NodeMap a → NodeMap a) → m ()
  modifyGraph   ∷ (g a b → g a b) → m ()
  getsNMState   ∷ ((NodeMap a, g a b) → r) → m r
  getsNodeMap   ∷ (NodeMap a → r) → m r
  getsGraph     ∷ (g a b → r) → m r
  --
  putNMState (nm, g) = putNodeMap nm >> putGraph g
  putNodeMap nm = modifyNMState (first (const nm))
  putGraph gr   = modifyNMState (second (const gr))
  getNMState    = liftM2 (,) getNodeMap getGraph
  getNodeMap    = getsNMState fst
  getGraph      = getsNMState snd
  modifyNMState = getsNMState >=> putNMState
  modifyNodeMap = getsNMState . first >=> putNMState
  modifyGraph   = getsNMState . second >=> putNMState
  getsNMState f = liftM f getNMState
  getsNodeMap f = liftM (f . fst) getNMState
  getsGraph f   = liftM (f . snd) getNMState
  --
  modifyNMG   ∷ (NodeMap a → g a b → (g a b, NodeMap a, r)) → m r
  modifyNMG f = do
    (nm, g) ← getNMState
    let (g', nm', r) = f nm g
    putNMState (nm', g')
    return r
  --
  modifyG     ∷ (NodeMap a → g a b → g a b) → m ()
  modifyG f   = do
    (nm, g) ← getNMState
    putGraph (f nm g)
  --
  modifyNM    ∷ (NodeMap a → (r, NodeMap a)) → m r
  modifyNM f  = do
    nm ← getNodeMap
    let (r, nm') = f nm
    putNodeMap nm'
    return r
  --
  mkNodeM         ∷ a → m (LNode a)
  mkNodesM        ∷ [a] → m [LNode a]
  mkEdgeM         ∷ (a, a, b) → m (Maybe (LEdge b))
  mkEdgesM        ∷ [(a, a, b)] → m (Maybe [LEdge b])
  insMapNodeM     ∷ a → m (LNode a)
  insNewMapNodeM  ∷ a → m (LNode a)
  insMapEdgeM     ∷ (a, a, b) → m ()
  delMapNodeM     ∷ a → m ()
  delMapEdgeM     ∷ (a, a) → m ()
  insMapNodesM    ∷ [a] → m [LNode a]
  insNewMapNodesM ∷ [a] → m [LNode a]
  insMapEdgesM    ∷ [(a, a, b)] → m ()
  delMapNodesM    ∷ [a] → m ()
  delMapEdgesM    ∷ [(a, a)] → m ()
  mkNodeM         = modifyNM . flip mkNode
  mkNodesM        = modifyNM . flip mkNodes
  mkEdgeM e       = getsNMState (flip mkEdge e . fst)
  mkEdgesM es     = getsNMState (flip mkEdges es . fst)
  insMapNodeM     = modifyNMG . flip insMapNode
  insNewMapNodeM  = modifyNMG . flip insNewMapNode
  insMapEdgeM     = modifyG . flip insMapEdge
  delMapNodeM     = modifyG . flip delMapNode
  delMapEdgeM     = modifyG . flip delMapEdge
  insMapNodesM    = modifyNMG . flip insMapNodes
  insNewMapNodesM = modifyNMG . flip insNewMapNodes
  insMapEdgesM    = modifyG . flip insMapEdges
  delMapNodesM    = modifyG . flip delMapNodes
  delMapEdgesM    = modifyG . flip delMapEdges

instance MonadNM a b g m ⇒ MonadNM a b g (ReaderT r m) where
  getNMState = lift getNMState
  putNMState = lift . putNMState

instance (MonadNM a b g m, Monoid w) ⇒ MonadNM a b g (Strict.WriterT w m) where
  getNMState = lift getNMState
  putNMState = lift . putNMState

instance (MonadNM a b g m, Monoid w) ⇒ MonadNM a b g (Lazy.WriterT w m) where
  getNMState = lift getNMState
  putNMState = lift . putNMState

instance MonadNM a b g m ⇒ MonadNM a b g (Strict.StateT s m) where
  getNMState = lift getNMState
  putNMState = lift . putNMState

instance MonadNM a b g m ⇒ MonadNM a b g (Lazy.StateT s m) where
  getNMState = lift getNMState
  putNMState = lift . putNMState

instance (MonadNM a b g m, Monoid w) ⇒ MonadNM a b g (Strict.RWST r w s m) where
  getNMState = lift getNMState
  putNMState = lift . putNMState

instance (MonadNM a b g m, Monoid w) ⇒ MonadNM a b g (Lazy.RWST r w s m) where
  getNMState = lift getNMState
  putNMState = lift . putNMState

---
--- Instances
---

instance (Ord a, DynGraph g, Monad m) ⇒
         MonadNM a b g (Strict.StateT (NodeMap a, g a b) m) where
  getNMState = get
  putNMState = put

instance (Ord a, DynGraph g, Monad m) ⇒
         MonadNM a b g (Lazy.StateT (NodeMap a, g a b) m) where
  getNMState = get
  putNMState = put
