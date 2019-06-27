module Test.Main where

import Prelude

import Control.Algebra.Properties as Props
import Data.Foldable (foldr)
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.Graph (Graph)
import Data.Graph as Graph
import Data.HeytingAlgebra (implies)
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, maybe)
import Data.Newtype (class Newtype, over, un)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, uncurry)
import Effect (Effect)
import Effect.Aff (Aff)
import Partial.Unsafe (unsafePartial, unsafePartialBecause)
import Test.QuickCheck (arbitrary, (<=?), (<?>), (===))
import Test.QuickCheck as QuickCheck
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.QuickCheck.Gen as Gen
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck')
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (run)

quickCheck'' :: forall t2. QuickCheck.Testable t2 => t2 -> Aff Unit
quickCheck'' = quickCheck' 2000

main :: Effect Unit
main = do
  run [consoleReporter] do
    describe "basic unit tests" do
      let n k v = Tuple k (Tuple k (Set.fromFoldable v ))
          --       4 - 8
          --      /     \
          -- 1 - 2 - 3 - 5 - 7
          --          \
          --           6
          acyclicGraph =
            Graph.fromMap (
              Map.fromFoldable
                [ n 1 [ 2 ]
                , n 2 [ 3, 4 ]
                , n 3 [ 5, 6 ]
                , n 4 [ 8 ]
                , n 5 [ 7 ]
                , n 6 [ ]
                , n 7 [ ]
                , n 8 [ 5 ]
                ])
          --       2 - 4
          --      / \
          -- 5 - 1 - 3
          cyclicGraph =
            Graph.fromMap (
              Map.fromFoldable
                [ n 1 [ 2 ]
                , n 2 [ 3, 4 ]
                , n 3 [ 1 ]
                , n 4 [ ]
                , n 5 [ 1 ]
                ])
      it "topologicalSort" do
        Graph.topologicalSort acyclicGraph `shouldEqual` List.fromFoldable [ 1, 2, 4, 8, 3, 6, 5, 7 ]
      it "insertEdgeWithVertices" do
        let t x = Tuple x x
            graph =
              Graph.insertEdgeWithVertices (t 1) (t 2) $
              Graph.insertEdgeWithVertices (t 2) (t 4) $
              Graph.insertEdgeWithVertices (t 4) (t 8) $
              Graph.insertEdgeWithVertices (t 8) (t 5) $
              Graph.insertEdgeWithVertices (t 5) (t 7) $
              Graph.insertEdgeWithVertices (t 2) (t 3) $
              Graph.insertEdgeWithVertices (t 3) (t 5) $
              Graph.insertEdgeWithVertices (t 3) (t 6) $
              Graph.empty
        G graph `shouldEqual` G acyclicGraph
        let graph' =
               Graph.insertEdgeWithVertices (t 5) (t 1) $
               Graph.insertEdgeWithVertices (t 1) (t 2) $
               Graph.insertEdgeWithVertices (t 2) (t 4) $
               Graph.insertEdgeWithVertices (t 2) (t 3) $
               Graph.insertEdgeWithVertices (t 3) (t 1) $
               Graph.empty
        G graph' `shouldEqual` G cyclicGraph
      it "descendants" do
        Graph.descendants 1 acyclicGraph `shouldEqual` Set.fromFoldable [ 2, 3, 4, 5, 6, 7, 8 ]
        Graph.descendants 2 acyclicGraph `shouldEqual` Set.fromFoldable [ 3, 4, 5, 6, 7, 8 ]
        Graph.descendants 3 acyclicGraph `shouldEqual` Set.fromFoldable [ 5, 6, 7 ]
        Graph.descendants 4 acyclicGraph `shouldEqual` Set.fromFoldable [ 5, 7, 8 ]
        Graph.descendants 5 acyclicGraph `shouldEqual` Set.fromFoldable [ 7 ]
        Graph.descendants 6 acyclicGraph `shouldEqual` Set.fromFoldable [ ]
        Graph.descendants 7 acyclicGraph `shouldEqual` Set.fromFoldable [ ]
        Graph.descendants 8 acyclicGraph `shouldEqual` Set.fromFoldable [ 5, 7 ]
      it "ancestors" do
        Graph.ancestors 1 acyclicGraph `shouldEqual` Set.fromFoldable [ ]
        Graph.ancestors 2 acyclicGraph `shouldEqual` Set.fromFoldable [ 1 ]
        Graph.ancestors 3 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2 ]
        Graph.ancestors 4 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2 ]
        Graph.ancestors 5 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2, 3, 4, 8 ]
        Graph.ancestors 6 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2, 3 ]
        Graph.ancestors 7 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2, 3, 4, 5, 8 ]
        Graph.ancestors 8 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2, 4 ]
      it "inCycle" do
        Graph.isInCycle 1 cyclicGraph `shouldEqual` true
        Graph.isInCycle 2 cyclicGraph `shouldEqual` true
        Graph.isInCycle 3 cyclicGraph `shouldEqual` true
        Graph.isInCycle 4 cyclicGraph `shouldEqual` false
        Graph.isInCycle 5 cyclicGraph `shouldEqual` false
      it "cyclic" do
        Graph.isCyclic cyclicGraph `shouldEqual` true
        Graph.isCyclic acyclicGraph `shouldEqual` false
        Graph.isAcyclic cyclicGraph `shouldEqual` false
        Graph.isAcyclic acyclicGraph `shouldEqual` true
      it "adjacent" do
        Graph.adjacent 1 acyclicGraph `shouldEqual` Set.fromFoldable [ 2 ]
        Graph.adjacent 2 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 3, 4 ]
        Graph.adjacent 3 acyclicGraph `shouldEqual` Set.fromFoldable [ 2, 5, 6 ]
        Graph.adjacent 4 acyclicGraph `shouldEqual` Set.fromFoldable [ 2, 8 ]
        Graph.adjacent 5 acyclicGraph `shouldEqual` Set.fromFoldable [ 3, 7, 8 ]
        Graph.adjacent 6 acyclicGraph `shouldEqual` Set.fromFoldable [ 3 ]
        Graph.adjacent 7 acyclicGraph `shouldEqual` Set.fromFoldable [ 5 ]
        Graph.adjacent 8 acyclicGraph `shouldEqual` Set.fromFoldable [ 4, 5 ]
        Graph.adjacent 1 cyclicGraph `shouldEqual` Set.fromFoldable [ 2, 3, 5 ]
        Graph.adjacent 2 cyclicGraph `shouldEqual` Set.fromFoldable [ 1, 3, 4 ]
        Graph.adjacent 3 cyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2 ]
        Graph.adjacent 4 cyclicGraph `shouldEqual` Set.fromFoldable [ 2 ]
        Graph.adjacent 5 cyclicGraph `shouldEqual` Set.fromFoldable [ 1 ]
      it "allPaths" do
        let nel x = unsafePartial $ fromJust <<< NEL.fromList <<< List.fromFoldable $ x
        Graph.allPaths 2 1 acyclicGraph `shouldEqual` Set.empty
        Graph.allPaths 1 9 acyclicGraph `shouldEqual` Set.empty
        Graph.allPaths 1 1 acyclicGraph `shouldEqual` Set.singleton (pure 1 )
        Graph.allPaths 1 2 acyclicGraph `shouldEqual` Set.singleton (nel [ 1, 2 ])
        Graph.allPaths 1 7 acyclicGraph `shouldEqual`
          Set.fromFoldable [ nel [ 1, 2, 4, 8, 5, 7 ], nel [ 1, 2, 3, 5, 7 ] ]
        Graph.allPaths 1 8 acyclicGraph `shouldEqual` Set.singleton (nel [ 1, 2, 4, 8 ])
        Graph.allPaths 2 6 acyclicGraph `shouldEqual` Set.singleton (nel [ 2, 3, 6 ])
        Graph.allPaths 5 3 cyclicGraph `shouldEqual` Set.singleton (nel [ 5, 1, 2, 3 ])
    describe "relationships" do
      it "shortestPath returns a valid path" do
        quickCheck'' ado
          Tuple k1 k2 <- arbitrary
          g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in (Foldable.all (Graph.isValidPath g) <<< Graph.shortestPath k1 k2 $ g)
      it "isParentOf implies isAncestorOf" do
        quickCheck'' ado
          Tuple k1 k2 <- arbitrary
          g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in
            (k1 `Graph.isParentOf g` k2) `implies` (k1 `Graph.isAncestorOf g` k2) <?>
            show (Tuple (Tuple k1 k2) (G g))
      it "isChildOf implies isDescendantOf" do
        quickCheck'' ado
          Tuple k1 k2 <- arbitrary
          g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in (k1 `Graph.isChildOf g` k2) `implies` (k1 `Graph.isDescendantOf g` k2)
      it "isAncestorOf and isDescendantOf are symmetric" do
        quickCheck'' ado
          Tuple k1 k2 <- arbitrary
          g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in k1 `Graph.isAncestorOf g` k2 === k2 `Graph.isDescendantOf g` k1
      it "isParentOf and isChildOf are symmetric" do
        quickCheck'' ado
          Tuple k1 k2 <- arbitrary
          g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in k1 `Graph.isParentOf g` k2 === k2 `Graph.isChildOf g` k1
      it "insertVertex and deleteVertex are opposites" do
        quickCheck'' do
          g' <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          Tuple k v <- arbitrary
          let g = Graph.deleteVertex k g'
          pure $ (G <<< Graph.deleteVertex k <<< Graph.insertVertex k v $ g) === G g
      it "insertVertex and vertices cohere" do
        quickCheck'' ado
          Tuple k v <- arbitrary
          g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in
            let
              len = List.length (Graph.vertices g)
              len' = List.length (Graph.vertices <<< Graph.insertVertex k v $ g)
            in
            len == len' || len + 1 == len'
      it "deleteVertex and vertices cohere" do
        quickCheck'' ado
          k <- arbitrary
          g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in
            let
              len = List.length (Graph.vertices g)
              len' = List.length (Graph.vertices <<< Graph.deleteVertex k $ g)
            in
            len == len' || len - 1 == len'
      it "deleteEdge and edges cohere" do
        quickCheck'' ado
          Tuple k1 k2 <- arbitrary
          g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in Set.delete (Tuple k1 k2) (Graph.edges g) === Graph.edges (Graph.deleteEdge k1 k2 g)
      it "insertEdgeWithVertices and edges cohere" do
        quickCheck'' ado
          Tuple k1 k2 <- arbitrary
          g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
          in
            Set.insert (Tuple (fst k1) (fst k2)) (Graph.edges g) ===
            Graph.edges (Graph.insertEdgeWithVertices k1 k2 g)
      it "insertEdge and deleteEdge are opposites" do
        let fromJust' x = unsafePartialBecause "genGraphAndEdge ensures keys present" $ fromJust x
        quickCheck'' do
          Tuple g' (Tuple k1 k2) <- genGraphAndEdge arbitrary arbitrary :: Gen (Tuple (Graph SmallInt SmallInt) _)
          let g = fromJust' <<< Graph.insertEdge k1 k2 $ g'
          pure $ (map G <<< Graph.insertEdge k1 k2 <<< Graph.deleteEdge k1 k2 $ g) === Just (G g)
        quickCheck'' do
          Tuple g' (Tuple k1 k2) <- genGraphAndEdge arbitrary arbitrary :: Gen (Tuple (Graph SmallInt SmallInt) _)
          let g = Graph.deleteEdge k1 k2 g'
          pure $ G (Graph.deleteEdge k1 k2 <<< fromJust' <<< Graph.insertEdge k1 k2 $ g) === G g
    describe "property tests" do
      describe "areConnected" do
        it "is transitive" do
          quickCheck'' ado
            Tuple k1 (Tuple k2 k3) <- arbitrary
            g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.transitive (Graph.areConnected g) k1 k2 k3
      describe "areAdjacent" do
        it "is antireflexive" do
          quickCheck'' ado
            k <- arbitrary
            g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.antireflexive (Graph.areAdjacent g) k || Graph.isCyclic g
        it "is commutative" do
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.commutative (Graph.areAdjacent g) k1 k2
      describe "isDescendantOf" do
        it "is transitive" do
          quickCheck'' ado
            Tuple k1 (Tuple k2 k3) <- arbitrary
            g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.transitive (Graph.isDescendantOf g) k1 k2 k3
        it "is asymmetric" do
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.asymmetric (Graph.isDescendantOf g) k1 k2
      describe "isChildOf" do
        it "is asymmetric" do
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.asymmetric (Graph.isChildOf g) k1 k2 || Graph.isCyclic g
      describe "isAncestorOf" do
        it "is transitive" do
          quickCheck'' ado
            Tuple k1 (Tuple k2 k3) <- arbitrary
            g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.transitive (Graph.isAncestorOf g) k1 k2 k3
        it "is asymmetric" do
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.asymmetric (Graph.isAncestorOf g) k1 k2
      describe "isParentOf" do
        it "is asymmetric" do
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.asymmetric (Graph.isParentOf g) k1 k2 || Graph.isCyclic g
      describe "deleteVertex" do
        it "deleting all vertices results in empty graph" do
          quickCheck'' ado
            g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in G (foldr Graph.deleteVertex g <<< Map.keys <<< Graph.toMap $ g) == G Graph.empty
        it "is idempotent" do
          quickCheck'' ado
            k <- arbitrary
            g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in idempotent (over G (Graph.deleteVertex k)) (G g)
        it "is congruent" do
          quickCheck'' ado
            k <- arbitrary
            g1 <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            g2 <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.congruent (over G (Graph.deleteVertex k)) (G g1) (G g2)
      describe "insertVertex" do
        it "is idempotent" do
          quickCheck'' ado
            Tuple k v <- arbitrary
            g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in idempotent (over G (Graph.insertVertex k v)) (G g)
        it "is congruent" do
          quickCheck'' ado
            Tuple k v <- arbitrary
            g1 <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            g2 <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.congruent (over G (Graph.insertVertex k v)) (G g1) (G g2)
      describe "deleteEdge" do
        it "is congruent" do
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            g1 <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            g2 <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Props.congruent (over G (Graph.deleteEdge k1 k2)) (G g1) (G g2)
        it "is idempotent" do
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            g <- genGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in idempotent (over G (Graph.deleteEdge k1 k2)) (G g)
      describe "insertEdge" do
        it "is idempotent" do
          let fromJust' x = unsafePartialBecause "genGraphAndEdge ensures keys present" $ fromJust x
          quickCheck'' ado
            Tuple g (Tuple k1 k2) <- genGraphAndEdge arbitrary arbitrary :: Gen (Tuple (Graph SmallInt SmallInt) _)
            in idempotent (G <<< fromJust' <<< Graph.insertEdge k1 k2 <<< un G) (G g)
      describe "shortestPath" do
        it "never gets longer with edge additions" do
          let fromJust' x = unsafePartialBecause "genGraphAndEdge ensures keys present" $ fromJust x
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            Tuple g (Tuple k3 k4) <- genAcyclicGraphAndEdge arbitrary arbitrary :: Gen (_ (Graph SmallInt SmallInt) _)
            in
              Graph.isCyclic (fromJust' $ Graph.insertEdge k3 k4 g) ||
                (maybe 9999 NEL.length $ Graph.shortestPath k1 k2 g) >=
                (maybe 9999 NEL.length $ Graph.shortestPath k1 k2 =<< Graph.insertEdge k3 k4 g)
        it "never gets shorter with edge deletions" do
          quickCheck'' ado
            Tuple k1 k2 <- arbitrary
            Tuple k3 k4 <- arbitrary
            g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in
              (NEL.length <$> Graph.shortestPath k1 k2 g) <=?
              (NEL.length <$> Graph.shortestPath k1 k2 (Graph.deleteEdge k3 k4 g))
      describe "topologicalSort" do
        it "returns all vertices" do
          quickCheck'' ado
            g <- genAcyclicGraph arbitrary arbitrary :: Gen (Graph SmallInt SmallInt)
            in Set.fromFoldable (Graph.topologicalSort g) === Map.keys (Graph.toMap g)

-- TODO: test alterVertex and alterEdges

genAcyclicGraphAndEdge :: forall k v. Ord k => Gen k -> Gen v -> Gen (Tuple (Graph k v) (Tuple k k))
genAcyclicGraphAndEdge genK genV = suchThat (genGraphAndEdge genK genV) (Graph.isAcyclic <<< fst)

genGraphAndEdge :: forall k v. Ord k => Gen k -> Gen v -> Gen (Tuple (Graph k v) (Tuple k k))
genGraphAndEdge genK genV = ado
    n1 <- Tuple <$> genK <*> genV
    n2 <- Tuple <$> genK <*> genV
    g <- genGraph genK genV
    in Tuple (uncurry Graph.insertVertex n2 <<< uncurry Graph.insertVertex n1 $ g) (Tuple (fst n1) (fst n2))

genAcyclicGraph :: forall k v. Ord k => Gen k -> Gen v -> Gen (Graph k v)
genAcyclicGraph genK genV = suchThat (genGraph genK genV) Graph.isAcyclic

genGraph :: forall k v. Ord k => Gen k -> Gen v -> Gen (Graph k v)
genGraph genK genV = ado
  l <- Gen.arrayOf genElement
  in Graph.fromMap <<< Map.fromFoldable $ l
    where
      genElement :: Gen (Tuple k (Tuple v (Set k)))
      genElement = ado
        k <- genK
        v <- genV
        ks <- genSet genK
        in (Tuple k (Tuple v ks))

genSet :: forall a. Ord a => Gen a -> Gen (Set a)
genSet genA = Set.fromFoldable <$> Gen.arrayOf genA

-- The implementation in the property library is maybe wrong?
idempotent :: forall a. Eq a => (a -> a) -> a -> Boolean
idempotent f a = f (f a) == f a

-- Convenient for use with specs
newtype GraphWrapper k v = G (Graph k v)
derive instance newtypeStringGraph :: Newtype (GraphWrapper k v) _
instance eqStringGraph :: (Eq k, Eq v) => Eq (GraphWrapper k v) where
  eq = eq `on` (Graph.toMap <<< un G)
instance showStringGraph :: (Show k, Show v) => Show (GraphWrapper k v) where
  show = show <<< Graph.toMap <<< un G

-- We want to make the graph denser so that we actually have edges and cycles
newtype SmallInt = MkSmallInt Int
derive instance eqSmallInt :: Eq SmallInt
derive instance ordSmallInt :: Ord SmallInt
derive instance genericSmallInt :: Generic SmallInt _
derive instance newtypeSmallInt :: Newtype SmallInt _
derive newtype instance semiringSmallInt :: Semiring SmallInt
derive newtype instance ringSmallInt :: Ring SmallInt
instance showSmallInt :: Show SmallInt where
  show (MkSmallInt i) = show i
instance arbitrarySmallInt :: QuickCheck.Arbitrary SmallInt where
  arbitrary = MkSmallInt <$> Gen.chooseInt 1 20
