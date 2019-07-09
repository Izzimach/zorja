{-# LANGUAGE TypeFamilies #-}

{-|
Module      : Zorja.Collections.Bag
Description : Sets where each element has a non-zero count
Stability   : Experimental

Bags are sets where each element has a non-zero count associated
with it. These are different from the normal multiset in that they
allow for negative values through excessive deletions.
-}

module Zorja.Collections.Bag (
    Bag (..),
    empty,
    singleton,
    singletonNeg,
    insert,
    delete,
    union,
    concat,
    map,
    member,
    negate
    )
    where

import Prelude hiding (concat, map, negate)
import qualified Prelude as Prelude

import Data.Semigroup
import Data.Monoid
import Data.Foldable hiding (concat)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Zorja.Patchable

-- | The element count of a specific element in the bag
type BagCount = Int

-- | A Bag is a Set where each element has an associated non-zero count
newtype Bag a = Bag { unBag :: Map a BagCount }

-- | Bags are their own deltas
type instance PatchDelta (Bag a) = Bag a

instance Ord a => Semigroup (Bag a) where
    (<>) = union

instance Ord a => Monoid (Bag a) where
    mempty = empty
    mappend = (<>)
    mconcat = concat

bagUpdate :: BagCount -> BagCount -> Maybe BagCount
bagUpdate x y = case (x + y) of
                    0 -> Nothing
                    n -> Just n

insert :: Ord a => a -> Bag a -> Bag a
insert x (Bag b) = Bag $ Map.update (bagUpdate 1) x b

delete :: Ord a => a -> Bag a -> Bag a
delete x (Bag b) = Bag $ Map.update (bagUpdate (-1)) x b

-- | Creates an empty Bag.
empty :: Bag a
empty = Bag Map.empty

-- | Create a bag with a single element
singleton :: a -> Bag a
singleton x = Bag $ Map.singleton x 1

-- | Create a bag with a single negative element
singletonNeg :: a -> Bag a
singletonNeg x = Bag $ Map.singleton x (-1)

-- | Combine two bags.  Elements that sum to 0 are removed.
union :: Ord a => Bag a -> Bag a -> Bag a
union (Bag m1) (Bag m2) = Bag $ Map.filter (==0) $ Map.unionWith (+) m1 m2

-- | Merge a list (or other @Foldable@ thing) of bags
concat :: (Ord a, Foldable f) => f (Bag a) -> Bag a
concat bs = foldl' union empty bs

-- | @fmap@ on a bag
map :: Ord b => (a -> b) -> Bag a -> Bag b
map f (Bag m) = Bag $ Map.mapKeysWith (+) f m

-- | Returns true if the key @k@ /has a count greater than zero/
member :: Ord a => a -> Bag a -> Bool
member x (Bag b) = case (Map.lookup x b) of
                       Nothing -> False
                       Just v  -> (v > 0)

-- | Negate all counts in the bag, basically negate the bag
negate :: Ord a => Bag a -> Bag a
negate (Bag m) = Bag $ Map.map Prelude.negate m

