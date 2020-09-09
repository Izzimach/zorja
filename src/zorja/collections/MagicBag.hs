{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-|
Module      : Zorja.Collections.MagicBag
Description : Sets where each element has a non-zero count
Stability   : Experimental

Magic bags are sets where each element has a non-zero count associated
with it. These are different from the normal multiset in that they
allow for negative values through excessive deletions.
-}

module Zorja.Collections.MagicBag (
    MagicBag (..),
    MagicDeltaBag (..),
    empty,
    singleton,
    singletonNeg,
    insert,
    delete,
    sumBags,
    maxBags,
    minBags,
    map,
    member,
    negate,
    fromList
    )
    where

import Prelude hiding (concat, map, negate, lookup)
import qualified Prelude as Prelude

import Data.Maybe
import Data.Semigroup
import Data.Monoid
import Data.Foldable hiding (concat)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Map.Merge.Strict

import Zorja.Patchable
import Zorja.Combine

-- | The element count of a specific element in the MagicBag
type MagicBagCount = Int

class AsMagicBag p where
    lookup :: Ord a => a -> p a -> Maybe MagicBagCount
    insert :: Ord a => a -> p a -> p a
    delete :: Ord a => a -> p a -> p a
    fromList :: Ord a => [a] -> p a
    maxBags :: Ord a => p a -> p a -> p a
    minBags :: Ord a => p a -> p a -> p a
    sumBags :: Ord a => p a -> p a -> p a
    map   :: (Ord a, Ord b) => (a -> b) -> p a -> p b
    negate :: (Ord a) => p a -> p a

-- | Creates an empty MagicBag.
empty :: (Ord a, AsMagicBag p) => p a
empty = fromList []

-- | Create a MagicBag with a single element
singleton :: (Ord a, AsMagicBag p) => a -> p a
singleton x = fromList [x]

-- | Create a MagicBag with a single negative element
singletonNeg :: (Ord a, AsMagicBag p) => a -> p a
singletonNeg x = delete x $ empty

-- | Returns true if the value @a@ /has a count greater than zero/
member :: (Ord a, AsMagicBag p) => a -> p a -> Bool
member p a = case (lookup p a) of
                       Nothing -> False
                       Just v  -> (v > 0)


-- | A MagicBag is a Set where each element has an associated non-zero count
newtype MagicBag a = MagicBag { unMagicBag :: Map a MagicBagCount }
    deriving (Eq, Show) via (Map a MagicBagCount)

-- | MagicBags are their own deltas
type instance ILCDelta (MagicBag a) = MagicBag a

instance Ord a => Semigroup (MagicBag a) where
    (<>) = sumBags

instance Ord a => Monoid (MagicBag a) where
    mempty = empty
    mappend = (<>)
    mconcat = foldl' sumBags empty

magicBagAlter :: MagicBagCount -> Maybe MagicBagCount -> Maybe MagicBagCount
magicBagAlter x my = let y = fromMaybe 0 my
                in case (x + y) of
                       0 -> Nothing
                       n -> Just n

mergeMagicBags :: (Ord a)
                => (MagicBagCount -> MagicBagCount -> MagicBagCount) 
                -> Map a MagicBagCount -> Map a MagicBagCount -> Map a MagicBagCount
mergeMagicBags f x y = Map.filter (== 0) $ Map.unionWith f x y

instance AsMagicBag MagicBag where
    lookup k (MagicBag a) = Map.lookup k a
    insert x (MagicBag b) = MagicBag $ Map.alter (magicBagAlter 1) x b
    delete x (MagicBag b) = MagicBag $ Map.alter (magicBagAlter (-1)) x b
    fromList as = MagicBag (Map.fromList (fmap (\x -> (x,1)) as))
    maxBags (MagicBag m1) (MagicBag m2) = MagicBag $ mergeMagicBags max m1 m2
    minBags (MagicBag m1) (MagicBag m2) = MagicBag $ mergeMagicBags min m1 m2
    sumBags (MagicBag m1) (MagicBag m2) = MagicBag $ mergeMagicBags (+) m1 m2
    map f (MagicBag m) = MagicBag $ Map.mapKeysWith (+) f m
    negate (MagicBag m) = MagicBag $ Map.map Prelude.negate m


-- | A MagicDeltaBag is a two magic bags smashed together. Used for representing a Bag and its delta
--   Changes modify the delta but not the value. lookups/reads use the value+delta result.
--   'union' and 'intersection' preoduce deltas from the left argument. So if @union a b = c@ then the-
--   deltas of @c@ will be changes from @a@ to @c@.
newtype MagicDeltaBag a = MagicDeltaBag { unMagicDeltaBag :: Map a (MagicBagCount, MagicBagCount) }
    
-- | Similar to the magicbag alter, but updates the delta to reflect the change.
-- Only remove the element is value + delta is 0. 
magicDeltaBagAlter :: MagicBagCount -> Maybe (MagicBagCount, MagicBagCount) -> Maybe (MagicBagCount, MagicBagCount)
magicDeltaBagAlter x my = let (y0,y1) = fromMaybe (0,0) my
                              y1' = y1 + x
                          in
                              if (y0 + y1' == 0)
                              then Nothing
                              else Just (y0,y1')
                          
type MagicDeltaBagMergeOp = (MagicBagCount, MagicBagCount) -> (MagicBagCount, MagicBagCount) -> (MagicBagCount, MagicBagCount)

maxDeltaMerge :: MagicDeltaBagMergeOp
maxDeltaMerge (a,da) (b,db) = if
                                  (a + da >= b + db)
                              then -- a+da is max, so choose it
                                  (a,da)
                              else -- b+db is max, so modify a's patch to result in d+db
                                  (a, b + db - a)

minDeltaMerge :: MagicDeltaBagMergeOp
minDeltaMerge (a,da) (b,db) = if
                                  (a + da < b + db)
                              then -- a+da is min, so choose it
                                  (a,da)
                              else -- b+db is min, so modify a's patch to result in d+db
                                  (a, b + db - a)

sumDeltaMerge :: MagicDeltaBagMergeOp
sumDeltaMerge (a,da) (b,db) = (a + b, da + db)

mergeDeltaBags :: (Ord a) => MagicDeltaBagMergeOp -> MagicDeltaBag a -> MagicDeltaBag a -> MagicDeltaBag a
mergeDeltaBags mf (MagicDeltaBag a) (MagicDeltaBag b) = MagicDeltaBag $ merge f1 f2 fb a b
    where
        f1 :: (Applicative f) => WhenMissing f k (MagicBagCount,MagicBagCount) (MagicBagCount,MagicBagCount)
        f1 = mapMissing (\k x -> mf x (0,0))
        f2 :: (Applicative f) => WhenMissing f k (MagicBagCount,MagicBagCount) (MagicBagCount,MagicBagCount)
        f2 = mapMissing (\k x -> mf (0,0) x)
        fb :: (Applicative f) => WhenMatched f k (MagicBagCount,MagicBagCount) (MagicBagCount,MagicBagCount)  (MagicBagCount, MagicBagCount)
        fb = zipWithMatched (\k x y -> mf x y)

instance AsMagicBag MagicDeltaBag where
    -- lookup returns the Patched count
    lookup x (MagicDeltaBag a) = fmap (\(x,y) -> x + y) $ Map.lookup x a
    insert x (MagicDeltaBag a) = MagicDeltaBag $ Map.alter (magicDeltaBagAlter 1) x a
    delete x (MagicDeltaBag a) = MagicDeltaBag $ Map.alter (magicDeltaBagAlter (-1)) x a
    -- creating a MagicDeltaBag from a list is equivalent to inserting all the elements into an empty bag.
    fromList as = (foldl' (flip insert) empty as)
    maxBags a b = mergeDeltaBags maxDeltaMerge a b
    minBags a b = mergeDeltaBags minDeltaMerge a b
    sumBags a b = mergeDeltaBags sumDeltaMerge a b
            


-- | Combining two MagicBags into a MagicDeltaBag
instance (Ord a) => T2Combine (MagicBag a) (MagicBag a) where
    type T2Combined (MagicBag a) (MagicBag a) = MagicDeltaBag a
    t2Combine (MagicBag as, MagicBag bs) = MagicDeltaBag $ merge f1 f2 fb as bs
        where
            f1 :: (Applicative f) => WhenMissing f k MagicBagCount (MagicBagCount,MagicBagCount)
            f1 = mapMissing (\k x -> (x,0 :: MagicBagCount))
            f2 :: (Applicative f) => WhenMissing f k MagicBagCount (MagicBagCount,MagicBagCount)
            f2 = mapMissing (\k x -> (0,x))
            fb :: (Applicative f) => WhenMatched f k MagicBagCount MagicBagCount  (MagicBagCount, MagicBagCount)
            fb = zipWithMatched (\k x y -> (x,y))
    t2Sunder (MagicDeltaBag ab) =
        let a = Map.mapMaybe (justNonzero . fst) ab
            b = Map.mapMaybe (justNonzero . snd) ab
        in (MagicBag a, MagicBag b)
            where
                justNonzero x
                    | x == 0    = Nothing
                    | otherwise = Just x


-- | Delta for a set; holds the elements to be inserted and deleted
data DeltaSet a = DeltaSet { inserts :: Set a, deletes :: Set a}
    deriving (Eq, Show)

-- | Functions as 'delete' for 'DeltaSet'. Should add the element to 'deletes' and
--   make sure it isn't in 'inserts'
moreDelete :: (Ord a) => a -> DeltaSet a -> DeltaSet a
moreDelete v (DeltaSet i d) = DeltaSet (Set.delete v i) (Set.insert v d)

-- | Functions as 'insert' for 'DeltaSet'
moreInsert :: (Ord a) => a -> DeltaSet a -> DeltaSet a
moreInsert v (DeltaSet i d) = DeltaSet (Set.insert v i) (Set.delete v d)

type instance ILCDelta (Set a) = DeltaSet a

instance (Ord a) => Semigroup (DeltaSet a) where
    (DeltaSet i1 d1) <> (DeltaSet i2 d2) =
        let i' = Set.difference (Set.union i1 i2) d2
            d' = Set.difference (Set.union d1 d2) i2
        in
            DeltaSet i' d'

instance (Ord a) => Monoid (DeltaSet a) where
    mempty = DeltaSet mempty mempty

data DSet a = DSet (Set a) (DeltaSet a)

instance T2Combine (Set a) (DeltaSet a) where
    type T2Combined (Set a) (DeltaSet a) = DSet a
    t2Combine (a,da) = DSet a da
    t2Sunder (DSet a da) = (a,da)

-- | Convert a 'MagicDeltaBag' to a 'Set' and 'DeltaSet'
distillBag :: (Ord a) => MagicDeltaBag a -> DSet a
distillBag (MagicDeltaBag m) = Map.foldrWithKey distillElement (DSet mempty mempty) m
    where
        distillElement :: (Ord a) => a -> (MagicBagCount, MagicBagCount) -> DSet a -> DSet a
        distillElement v (x,dx) (DSet s ds) =
            case (x == 0, x+dx == 0) of
                (True, False) -> DSet s (moreDelete v ds)
                (False, True) -> DSet s (moreInsert v ds)
                _             -> DSet s ds
