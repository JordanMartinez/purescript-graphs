-- | A data structure and functions for graphs

module Data.Graph
  ( Graph
  , unfoldGraph
  , fromMap
  , toMap
  , empty
  , insertEdge
  , insertVertex
  , insertEdgeWithVertices
  , vertices
  , lookup
  , outEdges
  , children
  , descendants
  , parents
  , ancestors
  , topologicalSort
  , isInCycle
  , isCyclic
  , isAcyclic
  , alterVertex
  , alterEdges
  , adjacent
  , isAdjacent
  , areConnected
  , shortestPath
  , allPaths
  , rootKeys
  , inDegreesKeys
  ) where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Internal as STI
import Control.Monad.ST.Internal as STRef
import Data.Array (foldl, length, unsafeIndex)
import Data.Array as Array
import Data.Array.ST as STA
import Data.Bifunctor (lmap, rmap)
import Data.CatList (CatList)
import Data.CatList as CL
import Data.Foldable (class Foldable)
import Data.Foldable as Foldable
import Data.FoldableWithIndex (foldlWithIndex)
import Data.HashMap (HashMap, insertWith, keys)
import Data.HashMap as Map
import Data.HashSet (HashSet)
import Data.HashSet as Set
import Data.Hashable (class Hashable, hash)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..), fromJust, isJust, maybe)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Partial.Unsafe (unsafePartial)

-- | A graph with vertices of type `v`.
-- |
-- | Edges refer to vertices using keys of type `k`.
newtype Graph k v = Graph (HashMap k (Tuple v (HashSet k)))

derive instance eqGraph :: (Eq k, Eq v) => Eq (Graph k v)
instance functorGraph :: Functor (Graph k) where
  map f (Graph m) = Graph (map (lmap f) m)

-- | An empty graph.
empty :: forall k v. Graph k v
empty = Graph Map.empty

-- | Insert an edge from the start key to the end key.
insertEdge :: forall k v. Hashable k => k -> k -> Graph k v -> Graph k v
insertEdge from to (Graph g) =
  Graph $ Map.alter (map (rmap (Set.insert to))) from g

-- | Insert a vertex into the graph.
-- |
-- | If the key already exists, replaces the existing value and
-- |preserves existing edges.
insertVertex :: forall k v. Hashable k => k -> v -> Graph k v -> Graph k v
insertVertex k v (Graph g) = Graph $ Map.insertWith (\(Tuple _ ks) _ -> Tuple v ks) k (Tuple v mempty) g

-- | Insert two vertices and connect them.
insertEdgeWithVertices :: forall k v. Hashable k => Tuple k v -> Tuple k v -> Graph k v -> Graph k v
insertEdgeWithVertices from@(Tuple fromKey _) to@(Tuple toKey _) =
  insertEdge fromKey toKey <<< uncurry insertVertex from <<< uncurry insertVertex to

-- | Unfold a `Graph` from a collection of keys and functions which label keys
-- | and specify out-edges.
unfoldGraph
  :: forall f k v out
   . Ord k
  => Functor f
  => Foldable f
  => Foldable out
  => Hashable k
  => f k
  -> (k -> v)
  -> (k -> out k)
  -> Graph k v
unfoldGraph ks label edges =
  Graph (Map.fromFoldable (map (\k ->
            Tuple k (Tuple (label k) (Set.fromFoldable (edges k)))) ks))

-- | Create a `Graph` from a `Map` which maps vertices to their labels and
-- | outgoing edges.
fromMap :: forall k v. HashMap k (Tuple v (HashSet k)) -> Graph k v
fromMap = Graph

-- | Turn a `Graph` into a `Map` which maps vertices to their labels and
-- | outgoing edges.
toMap :: forall k v. Graph k v -> HashMap k (Tuple v (HashSet k))
toMap (Graph g) = g

-- | Check if the first key is adjacent to the second.
isAdjacent :: forall k v. Hashable k => k -> k -> Graph k v -> Boolean
isAdjacent k1 k2 g = k1 `Set.member` adjacent k2 g

-- | Find all keys adjacent to given key.
adjacent :: forall k v. Hashable k => k -> Graph k v -> HashSet k
adjacent k g = children k g `Set.union` parents k g

-- | Returns shortest path between start and end key if it exists.
-- |
-- | Cyclic graphs may return bottom.
shortestPath :: forall k v. Hashable k => k -> k -> Graph k v -> Maybe (List k)
shortestPath start end g =
  Array.head <<< Array.sortWith List.length <<< Set.toUnfoldable $ allPaths start end g

-- | Returns shortest path between start and end key if it exists.
-- |
-- | Cyclic graphs may return bottom.
allPaths :: forall k v. Hashable k => k -> k -> Graph k v -> HashSet (List k)
allPaths start end g = Set.map List.reverse $ go mempty start
  where
    go hist k =
      if end == k
      then Set.singleton hist'
      else
        if children' == Set.empty
        then Set.empty
        else Foldable.foldMap (go hist') children'
      where
        children' = children k g
        hist' = k `Cons` hist

-- | Checks if there's a directed path between the start and end key.
areConnected :: forall k v. Hashable k => k -> k -> Graph k v -> Boolean
areConnected start end g = isJust $ shortestPath start end g

-- | List all vertices in a graph.
vertices :: forall k v. Graph k v -> Array v
vertices (Graph g) = map fst (Map.values g)

-- | Lookup a vertex by its key.
lookup :: forall k v. Hashable k => k -> Graph k v -> Maybe v
lookup k (Graph g) = map fst (Map.lookup k g)

-- | Get the keys which are directly accessible from the given key.
outEdges :: forall k v. Hashable k => k -> Graph k v -> Maybe (HashSet k)
outEdges k (Graph g) = map snd (Map.lookup k g)

-- | Returns immediate ancestors of given key.
parents :: forall k v. Hashable k => k -> Graph k v -> HashSet k
parents k (Graph g) = Set.fromArray <<< Map.keys <<< Map.filter (Foldable.elem k <<< snd) $ g

-- | Returns all ancestors of given key.
-- |
-- | Will return bottom if `k` is in cycle.
ancestors :: forall k v. Hashable k => k -> Graph k v -> HashSet k
ancestors k' g = go k'
  where
   go k = Set.unions $ Set.insert da $ Set.map go da
     where
       da = parents k g

-- | Returns immediate descendants of given key.
children :: forall k v. Hashable k => k -> Graph k v -> HashSet k
children k (Graph g) = maybe mempty (Set.fromFoldable <<< snd) <<< Map.lookup k $ g

-- | Returns all descendants of given key.
-- |
-- | Will return bottom if `k` is in cycle.
descendants :: forall k v. Hashable k => k -> Graph k v -> HashSet k
descendants k' g = go k'
  where
   go k = Set.unions $ Set.insert dd $ Set.map go dd
     where
       dd = children k g

-- | Checks if given key is part of a cycle.
isInCycle :: forall k v. Hashable k => k -> Graph k v -> Boolean
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
isCyclic :: forall k v. Hashable k => Graph k v -> Boolean
isCyclic g = Foldable.any (flip isInCycle g) <<< keys $ g
  where
    keys (Graph g') = Map.keys g'

-- | Checks if there are not any cycles in the graph.
isAcyclic :: forall k v. Hashable k => Graph k v -> Boolean
isAcyclic = not <<< isCyclic

alterVertex ::
  forall v k.
  Hashable k =>
  (Maybe v -> Maybe v) ->
  k -> Graph k v -> Graph k v
alterVertex f k (Graph g) = Graph $ Map.alter (applyF =<< _) k g
  where
    applyF (Tuple v es) = flip Tuple es <$> f (Just v)

alterEdges ::
  forall v k.
  Hashable k =>
  (Maybe (HashSet k) -> Maybe (HashSet k)) ->
  k -> Graph k v -> Graph k v
alterEdges f k (Graph g) = Graph $ Map.alter (applyF =<< _) k g
  where
    applyF (Tuple v es) = Tuple v <$> f (Just es)

type SortState k v =
  { unvisited :: HashMap k (Tuple v (HashSet k))
  , result :: List k
  }

-- To defunctionalize the `topologicalSort` function and make it tail-recursive,
-- we introduce this data type which captures what we intend to do at each stage
-- of the recursion.
data SortStep a = Emit a | Visit a
derive instance eqSortStep :: Eq a => Eq (SortStep a)
derive instance ordSortStep :: Ord a => Ord (SortStep a)
instance hashableSortSet :: Hashable a => Hashable (SortStep a) where
  hash = case _ of
    Emit a -> hash a * 13
    Visit a -> hash a * 31

-- | Topologically sort the vertices of a graph.
-- |
-- | If the graph contains cycles, then the behavior is undefined.
topologicalSort :: forall k v. Hashable k => Graph k v -> List k
topologicalSort (Graph g) =
    go { unvisited: g, result: Nil }
  where
    findRootEdge :: Hashable k => HashMap k (Tuple v (HashSet k)) -> Maybe k
    findRootEdge hashmap =
      let inDegrees = foldlWithIndex countEdges Map.empty hashmap
      in ST.run do
        found <- STRef.new false
        idx <- STRef.new 0
        val <- STRef.new Nothing
        let
          ks = keys inDegrees
          len = length ks
          shouldLoop = ado
            notFound <- not <$> STRef.read found
            validIndex <- (_ /= len) <$> STRef.read idx
            in notFound && validIndex
        STI.while shouldLoop do
          currentIdx <- STRef.read idx
          let currentKey = unsafePartial $ unsafeIndex ks currentIdx
          case unsafePartial $ fromJust $ Map.lookup currentKey inDegrees of
            0 -> do
              _ <- STI.write (Just currentKey) val
              void $ STI.write true found
            _ -> do
              void $ STRef.modify (_ + 1) idx
        STRef.read val

    countEdges :: k -> HashMap k Int -> (Tuple v (HashSet k)) -> HashMap k Int
    countEdges _ acc (Tuple _ edgeSet) =
      foldl (\acc' e -> insertWith (\orig _ -> orig + 1) e 0 acc') acc edgeSet

    go :: SortState k v -> List k
    go state@{ unvisited, result } =
      case findRootEdge unvisited of
        Just key -> go (visit state (CL.fromFoldable [Visit key]))
        Nothing -> result

    visit :: SortState k v -> CatList (SortStep k) -> SortState k v
    visit state stack =
      case CL.uncons stack of
        Nothing -> state
        Just (Tuple (Emit k) ks) ->
          visit (state { result = Cons k state.result }) ks
        Just (Tuple (Visit k) ks)
          | k `Map.member` state.unvisited ->
            let start :: SortState k v
                start = state { unvisited = Map.delete k state.unvisited }

                next :: HashSet k
                next = maybe mempty snd (Map.lookup k g)

            in visit start (CL.fromFoldable (Set.map Visit next) <> CL.cons (Emit k) ks)
          | otherwise -> visit state ks

-- | Returns the keys of all roots found in the graph. If the graph is cyclical,
-- | an empty array will be returned.
rootKeys :: forall k v. Hashable k => Graph k v -> Array k
rootKeys graph = STA.run do
  foldlWithIndex includeKeyIfValueIsZero STA.empty (inDegreesKeys graph)
  where
  includeKeyIfValueIsZero :: forall h. k -> STI.ST h (STA.STArray h k) -> Int -> STI.ST h (STA.STArray h k)
  includeKeyIfValueIsZero k getArray v
    | v /= 0 = getArray
    | otherwise = do
        arr <- getArray
        _ <- STA.push k arr
        pure arr

-- | Calculates how many keys in the graph point to a given node in the graph
inDegreesKeys :: forall k v. Hashable k => Graph k v -> HashMap k Int
inDegreesKeys (Graph hashmap) =
  foldlWithIndex countEdges (map (const 0) hashmap) hashmap
  where
  countEdges :: k -> HashMap k Int -> (Tuple v (HashSet k)) -> HashMap k Int
  countEdges _ acc (Tuple _ edgeSet) =
    foldl addOneToEachChildEdge acc edgeSet
    where
      addOneToEachChildEdge accMap e =
        Map.alter (map (_ + 1)) e accMap
