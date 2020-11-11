module Data.HashSet.Extra where

import Prelude

import Data.Array (foldl)
import Data.Array as Array
import Data.Foldable (class Foldable)
import Data.HashSet (HashSet, empty, toArray, union)
import Data.Hashable (class Hashable)
import Data.Unfoldable (class Unfoldable)

toUnfoldable :: forall f a. Unfoldable f => HashSet a -> f a
toUnfoldable = Array.toUnfoldable <<< toArray

unions :: forall f a. Foldable f => Hashable a => f (HashSet a) -> HashSet a
unions = foldl union empty
