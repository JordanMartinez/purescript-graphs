-- | A data structure and functions for graphs

module Data.Graph
  ( Graph
  , unfoldGraph
  , fromMap
  , toMap
  , empty
  , insertEdge
  , deleteEdge
  , insertVertex
  , deleteVertex
  , insertEdgeWithVertices
  , vertices
  , edges
  , lookup
  , outEdges
  , children
  , isChildOf
  , descendants
  , isDescendantOf
  , parents
  , isParentOf
  , ancestors
  , isAncestorOf
  , topologicalSort
  , isInCycle
  , isCyclic
  , isAcyclic
  , alterVertex
  , alterEdges
  , adjacent
  , areAdjacent
  , areConnected
  , isValidPath
  , shortestPath
  , allPaths
  ) where

import Prelude

import Data.Array as Array
import Data.Bifunctor (lmap, rmap)
import Data.CatList (CatList)
import Data.CatList as CL
import Data.Foldable (class Foldable, foldl)
import Data.Foldable as Foldable
import Data.List (List(..))
import Data.List as L
import Data.List.NonEmpty (NonEmptyList(..))
import Data.List.NonEmpty as NEL
import Data.List.Types (nelCons)
import Data.Map (Map)
import Data.Map as M
import Data.Maybe (Maybe(..), fromJust, isJust, maybe)
import Data.NonEmpty ((:|))
import Data.Set (Set)
import Data.Set as S
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Partial.Unsafe (unsafePartialBecause)

-- | A graph with vertices of type `v`.
-- |
-- | Edges refer to vertices using keys of type `k`.
newtype Graph k v = Graph (Map k (Tuple v (Set k)))

instance functorGraph :: Functor (Graph k) where
  map f (Graph m) = Graph (map (lmap f) m)

-- | An empty graph.
empty :: forall k v. Graph k v
empty = Graph M.empty

-- | Insert an edge from the start key to the end key.
-- |
-- | Does nothing if the edge is already present.
-- | Returns `Nothing` iff either key is absent from the graph.
insertEdge :: forall k v. Ord k => k -> k -> Graph k v -> Maybe (Graph k v)
insertEdge from to (Graph g) =
  if from `Set.member` keys && to `Set.member` keys
  then Just $ Graph $ M.alter (map (rmap (S.insert to))) from g
  else Nothing
  where
    keys = M.keys g

-- | Remove edge from the start key to the end key.
-- |
-- | Does nothing if the edge isn't present.
deleteEdge :: forall k v. Ord k => k -> k -> Graph k v -> Graph k v
deleteEdge from to (Graph g) =
  Graph $ M.alter (map (rmap (S.delete to))) from g

-- | Insert a vertex into the graph.
-- |
-- | If the key already exists, replaces the existing value and
-- | preserves existing edges.
insertVertex :: forall k v. Ord k => k -> v -> Graph k v -> Graph k v
insertVertex k v (Graph g) =
  Graph $ M.insertWith (\(Tuple _ ks) _ -> Tuple v ks) k (Tuple v mempty) g

-- | Remove the given vertex from the graph.
-- |
-- | Does nothing if the key isn't present.
deleteVertex :: forall k v. Ord k => k -> Graph k v -> Graph k v
deleteVertex k (Graph g) = Graph $ M.delete k g

-- | Insert two vertices and connect them.
insertEdgeWithVertices :: forall k v. Ord k => Tuple k v -> Tuple k v -> Graph k v -> Graph k v
insertEdgeWithVertices from@(Tuple fromKey _) to@(Tuple toKey _) g =
  unsafePartialBecause "Just inserted vertices" $ fromJust <<<
  insertEdge fromKey toKey <<< uncurry insertVertex from <<< uncurry insertVertex to $ g

-- | Unfold a `Graph` from a collection of keys and functions which label keys
-- | and specify out-edges.
unfoldGraph
  :: forall f k v out
   . Ord k
  => Functor f
  => Foldable f
  => Foldable out
  => f k
  -> (k -> v)
  -> (k -> out k)
  -> Graph k v
unfoldGraph ks label edges' =
  Graph (M.fromFoldable (map (\k ->
    Tuple k (Tuple (label k) (S.fromFoldable (edges' k)))) ks))

-- | Create a `Graph` from a `Map` which maps vertices to their labels and
-- | outgoing edges.
fromMap :: forall k v. Map k (Tuple v (Set k)) -> Graph k v
fromMap = Graph

-- | Turn a `Graph` into a `Map` which maps vertices to their labels and
-- | outgoing edges.
toMap :: forall k v. Graph k v -> Map k (Tuple v (Set k))
toMap (Graph g) = g

-- | Check if the keys are adjacent.
-- |
-- | Returns `false` if either key is absent from the graph.
areAdjacent :: forall k v. Ord k => Graph k v -> k -> k -> Boolean
areAdjacent g k1 k2 = k1 `Set.member` adjacent k2 g

-- | Find all keys adjacent to given key.
-- |
-- | Returns `mempty` if the key is absent from the graph.
adjacent :: forall k v. Ord k => k -> Graph k v -> Set k
adjacent k g = children k g `Set.union` parents k g

isValidPath :: forall k v. Ord k => Graph k v -> NonEmptyList k -> Boolean
isValidPath g (NonEmptyList (k :| ks)) =
  fst $ foldl (\(Tuple b p) c -> Tuple (p `isParentOf g` c) c) (Tuple true k) ks

-- | Returns shortest path between start and end key if it exists.
-- |
-- | Returns `Nothing` if there's no path between the keys or
-- | if the keys aren't present in the graph.
-- | Cyclic graphs may return bottom.
shortestPath :: forall k v. Ord k => k -> k -> Graph k v -> Maybe (NonEmptyList k)
shortestPath start end g =
  Array.head <<< Array.sortWith (asInt <<< Foldable.length) <<< S.toUnfoldable $
  allPaths start end g
  where
    asInt :: Int -> Int
    asInt = identity

-- | Returns shortest path between start and end key if it exists.
-- |
-- | Cyclic graphs may return bottom.
-- | Returns `mempty` if either key is absent from the graph.
allPaths :: forall k v. Ord k => k -> k -> Graph k v -> Set (NonEmptyList k)
allPaths start end g = Set.map NEL.reverse $ go Nothing start
  where
    go hist k =
      if end == k
      then Set.singleton hist'
      else
        if children' == Set.empty
        then Set.empty
        else Foldable.foldMap (go $ Just hist') children'
      where
        children' = children k g
        hist' = maybe (pure k) (nelCons k) hist

-- | Checks if there's a directed path between the start and end key.
areConnected :: forall k v. Ord k => Graph k v -> k -> k -> Boolean
areConnected g start end = isJust $ shortestPath start end g

-- | List all vertices in a graph.
vertices :: forall k v. Graph k v -> List v
vertices (Graph g) = map fst (M.values g)

-- | List all edges in a graph.
edges :: forall k v. Ord k => Graph k v -> Set (Tuple k k)
edges (Graph g) =
  Set.fromFoldable $ (\(Tuple k x) -> map (Tuple k) <<< L.fromFoldable <<< snd $ x) =<<
  M.toUnfoldable g

-- | Lookup a vertex by its key.
lookup :: forall k v. Ord k => k -> Graph k v -> Maybe v
lookup k (Graph g) = map fst (M.lookup k g)

-- | Get the keys which are directly accessible from the given key.
outEdges :: forall k v. Ord k => k -> Graph k v -> Maybe (Set k)
outEdges k (Graph g) = map snd (M.lookup k g)

-- | Returns immediate ancestors of given key.
-- |
-- | Returns `mempty` if the queried key is absent from the graph.
parents :: forall k v. Ord k => k -> Graph k v -> Set k
parents k (Graph g) = M.keys <<< M.filter (Foldable.elem k <<< snd) $ g

-- | Returns `false` if either key is absent from the graph.
isParentOf :: forall k v. Ord k => Graph k v -> k -> k -> Boolean
isParentOf g k1 k2 = k1 `Set.member` parents k2 g

-- | Returns all ancestors of given key.
-- |
-- | Returns bottom if `k` is in cycle.
-- | Returns `mempty` if the queried key is absent from the graph.
ancestors :: forall k v. Ord k => k -> Graph k v -> Set k
ancestors k' g = go k'
  where
   go k = Set.unions $ Set.insert da $ Set.map go da
     where
       da = parents k g

-- | Returns `false` if either key is absent from the graph.
isAncestorOf :: forall k v. Ord k => Graph k v -> k -> k -> Boolean
isAncestorOf g k1 k2 = k1 `Set.member` ancestors k2 g

-- | Returns immediate descendants of given key.
-- |
-- | Returns `mempty` if the queried key is absent from the graph.
children :: forall k v. Ord k => k -> Graph k v -> Set k
children k (Graph g) = maybe mempty (Set.fromFoldable <<< snd) <<< M.lookup k $ g

-- | Returns `false` if either key is absent from the graph.
isChildOf :: forall k v. Ord k => Graph k v -> k -> k -> Boolean
isChildOf g k1 k2 = k1 `Set.member` children k2 g

-- | Returns all descendants of given key.
-- |
-- | Returns bottom if `k` is in cycle.
-- | Returns `mempty` if the queried key is absent from the graph.
descendants :: forall k v. Ord k => k -> Graph k v -> Set k
descendants k' g = go k'
  where
   go k = Set.unions $ Set.insert dd $ Set.map go dd
     where
       dd = children k g

-- | Returns `false` if either key is absent from the graph.
isDescendantOf :: forall k v. Ord k => Graph k v -> k -> k -> Boolean
isDescendantOf g k1 k2 = k1 `Set.member` descendants k2 g

-- | Checks if given key is part of a cycle.
isInCycle :: forall k v. Ord k => k -> Graph k v -> Boolean
isInCycle k' g = go mempty k'
  where
    go seen k =
      case Tuple (dd == mempty) (k `Set.member` seen) of
        Tuple true _ -> false
        Tuple _ true -> k == k'
        Tuple false false -> Foldable.any (go (Set.insert k seen)) dd
      where
        dd = children k g

-- | Checks if there any cycles in graph.
-- There's presumably a faster implementation but this is very easy to implement
isCyclic :: forall k v. Ord k => Graph k v -> Boolean
isCyclic g = Foldable.any (flip isInCycle g) <<< keys $ g
  where
    keys (Graph g') = M.keys g'

-- | Checks if there are not any cycles in the graph.
isAcyclic :: forall k v. Ord k => Graph k v -> Boolean
isAcyclic = not <<< isCyclic

alterVertex ::
  forall v k.
  Ord k =>
  (Maybe v -> Maybe v) ->
  k -> Graph k v -> Graph k v
alterVertex f k (Graph g) = Graph $ M.alter (applyF =<< _) k g
  where
    applyF (Tuple v es) = flip Tuple es <$> f (Just v)

alterEdges ::
  forall v k.
  Ord k =>
  (Maybe (Set k) -> Maybe (Set k)) ->
  k -> Graph k v -> Graph k v
alterEdges f k (Graph g) = Graph $ M.alter (applyF =<< _) k g
  where
    applyF (Tuple v es) = Tuple v <$> f (Just es)

type SortState k v =
  { unvisited :: Map k (Tuple v (Set k))
  , result :: List k
  }

-- To defunctionalize the `topologicalSort` function and make it tail-recursive,
-- we introduce this data type which captures what we intend to do at each stage
-- of the recursion.
data SortStep a = Emit a | Visit a
derive instance eqSortStep :: Eq a => Eq (SortStep a)
derive instance ordSortStep :: Ord a => Ord (SortStep a)

-- | Topologically sort the vertices of a graph.
-- |
-- | If the graph contains cycles, then the behavior is undefined.
topologicalSort :: forall k v. Ord k => Graph k v -> List k
topologicalSort (Graph g) =
    go initialState
  where
    go :: SortState k v -> List k
    go state@{ unvisited, result } =
      case M.findMin unvisited of
        Just { key } -> go (visit state (CL.fromFoldable [Visit key]))
        Nothing -> result

    visit :: SortState k v -> CatList (SortStep k) -> SortState k v
    visit state stack =
      case CL.uncons stack of
        Nothing -> state
        Just (Tuple (Emit k) ks) ->
          let state' = { result: Cons k state.result
                       , unvisited: state.unvisited
                       }
          in visit state' ks
        Just (Tuple (Visit k) ks)
          | k `M.member` state.unvisited ->
            let start :: SortState k v
                start =
                  { result: state.result
                  , unvisited: M.delete k state.unvisited
                  }

                next :: Set k
                next = maybe mempty snd (M.lookup k g)
            in visit start (CL.fromFoldable (Set.map Visit next) <> CL.cons (Emit k) ks)
          | otherwise -> visit state ks

    initialState :: SortState k v
    initialState = { unvisited: g
                   , result: Nil
                   }
