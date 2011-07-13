{-# LANGUAGE
      UnicodeSyntax
    #-}
-- | A wrapper around the fgs graph library.
module Alt.Graph (
  ShowGraph(..),
  trcnr, untransitive, nmLab, labelNode, labScc,
  pathScc, erdffWith, xpdffWith, xpdfWith,
  labComponents, labNodeEdges,
  module Data.Graph.Inductive.Basic,
  module Data.Graph.Inductive.Graph,
  module Data.Graph.Inductive.Query.DFS,
  module Data.Graph.Inductive.Query.TransClos,
  module NM,
) where


-- Mine:
import Util
import Alt.NodeMap as NM

import Prelude ()
import qualified Data.List as List
import qualified Data.Tree as Tree

-- From fgs:
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.TransClos

-- | Transitive, non-reflexive closure
trcnr ∷ DynGraph gr ⇒ gr a b → gr a ()
trcnr g = insEdges newEdges (insNodes lns empty) where
  lns      = labNodes g
  newEdges = [ (n, n', ())
             | (n, _) ← lns
             , n'     ← reachable n g
             , n /= n' ]

-- | Compute the transitive reduction of a transitive, acyclic graph.
untransitive ∷ DynGraph gr ⇒ gr a b → gr a b
untransitive g = foldl' eachEdge g (edges g) where
  eachEdge g' (n1, n2) = foldl' eachSuc g' (suc g' n1) where
    eachSuc g'' n' =
      if n' /= n1 && n' /= n2 && n2 `elem` suc g'' n'
        then delEdge (n1, n2) g''
        else g''

-- | Look up the node index of a node label
nmLab ∷ Ord a ⇒ NM.NodeMap a → a → Node
nmLab = fst <$$> NM.mkNode_

labelNode ∷ Graph gr ⇒ gr a b → Node → LNode a
labelNode g n = case lab g n of
  Just ln → (n, ln)
  Nothing → error "labelNode: node not found"

labScc ∷ Graph gr ⇒ gr a b → [[LNode a]]
labScc g = map preorder (rdffWith labNode' (topsort g) g)

pathScc ∷ Graph gr ⇒ gr a b → [Either (LNode a) [(LNode a, b)]]
pathScc g = map (addCycle . preorder) (erdffWith labNode' (topsort g) g)
  where
  addCycle [((n, a), Nothing)] =
    case lookup n (lpre g n) of
      Just b  → Right [((n, a), b)]
      Nothing → Left (n, a)
  addCycle (((n, a), Nothing):rest) =
    case catMaybes [ lookup n' (lsuc g n) | ((n', _), _) ← rest ] of
      b:_  → Right (((n, a), b) : map (second fromJust) rest)
      []   → error "pathScc: bug!"
  addCycle _ = error "pathScc: bug!"

erdffWith ∷ Graph gr ⇒
            CFun a b c → [Node] → gr a b → [Tree.Tree (c, Maybe b)]
erdffWith = xpdffWith (map (second Just) . lpre') <$.> map (\n → (n, Nothing))

rdffWith ∷ Graph gr ⇒ CFun a b c → [Node] → gr a b → [Tree.Tree c]
rdffWith = xdffWith pre'

_g ∷ Gr Int String
_g = mkGraph ns es where
  ns = (id &&& id) <$> [0 .. 20]
  es = map addLab $
         [ (0,5), (1,5), (2,5), (3,5), (4,5),
           (0,6), (1,6), (2,6), (3,6), (4,6),
           (5,7), (6,7), (5,8), (6,8),
           (7,9), (8,9), (7,10), (8,10),
           (9,0), (9,1), (9,2), (9,3), (9,4),
           (10,0), (10,1), (10,2), (10,3), (10,4)
         ]
  addLab (i, j) = (i, j, show i ++ "->" ++ show j)

-- | A generalized, path-sensitive depth-first forest.  Along with
--   each starting node, it takes a value to associate with that node,
--   and the next-finding function produces new values to go with
--   each node as well.
xpdffWith ∷ Graph gr ⇒
           CFun a b [(Node, d)] → CFun a b c →
           [(Node, d)] → gr a b → [Tree.Tree (c, d)]
xpdffWith = fst <$$$$> xpdfWith

xpdfWith ∷ Graph gr ⇒
           CFun a b [(Node, d)] → CFun a b c →
           [(Node, d)] → gr a b → ([Tree.Tree (c, d)], gr a b)
xpdfWith _ _ []     g             = ([],g)
xpdfWith _ _ _      g | isEmpty g = ([],g)
xpdfWith d f ((v,e):vs) g =
  case match v g of
    (Nothing, g1) → xpdfWith d f vs g1
    (Just c, g1)  → (Tree.Node (f c, e) ts:ts', g3)
      where (ts, g2)  = xpdfWith d f (d c) g1
            (ts', g3) = xpdfWith d f vs g2

-- | Partition a graph into components of /labeled/ nodes
labComponents ∷ Graph gr ⇒ gr a b → [[LNode a]]
labComponents = componentsWith labNode'
  where
  udffWith ∷ Graph gr ⇒ CFun a b c → [Node] → gr a b → [Tree.Tree c]
  udffWith = xdffWith neighbors'
  --
  udffWith' ∷ Graph gr ⇒ CFun a b c → gr a b → [Tree.Tree c]
  udffWith' f g = udffWith f (nodes g) g
  --
  componentsWith ∷ Graph gr ⇒ CFun a b c → gr a b → [[c]]
  componentsWith = preorder <$$$> udffWith'

-- | Get the edges of a graph as pairs of node labels
labNodeEdges ∷ Graph gr ⇒ gr n e → [(n, n)]
labNodeEdges g =
  [ (α, β)
  | (n1, n2) ← edges g
  , let Just α = lab g n1
  , let Just β = lab g n2
  ]

-- | For showing graphs
newtype ShowGraph gr v = ShowGraph { unShowGraph ∷ gr v () }

instance (Graph gr, Show v) ⇒ Show (ShowGraph gr v) where
  showsPrec _ (ShowGraph gr) =
    showChar '{' .
    foldr (.) id
      (List.intersperse (showString ", ")
         [ shows n1 . showString "<" . shows n2
         | (n1, n2) ← labNodeEdges gr ])
    . showChar '}'

