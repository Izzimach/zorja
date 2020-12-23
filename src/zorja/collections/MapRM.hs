

{-|
Module      : Zorja.Collections.MapRM
Description : Handle a map of ReplaceableMaybe elements.
Copyright   : (c) Gary Haussmann, 2019
Stability   : experimental

Intuitively the 'ValDelta' of a @Map a@ would be @Map (ValDelta a)@ but this
can't record the adding or removing of elements from the map. To handle
adds/removes one needs to record the empty spaces that exists before an 'insert'
or after a 'delete'. If we use 'Nothing' to record an empty space then
@a@ becomes @Maybe a@ before and after which can be represented as
a 'ReplaceableMaybe'. The operations in here will update the 'ReplaceableMaybe'
values appropriately and allow access via lenses.

-}

module Zorja.Collections.MapRM 
    (
        insert,
        lookup,
        adjust,
        delete,
        update,
        alter
    ) where

import qualified Data.Map as Map

import Zorja.Patchable
import Zorja.Primitives


insert :: (Ord k, Patchable a, ValDeltaBundle a) => 
  k -> a -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
insert k v m = 
  let r = (fromMaybeCRM (Map.lookup k m))
  in
    Map.insert k (set replaceableMaybe (Just v) r) m

lookup :: (Ord k, Patchable a, ValDeltaBundle a) =>
  k -> Map.Map k (ReplaceableMaybe a) -> Maybe a
lookup k m = let (ReplaceableMaybe v) = (fromMaybeCRM (Map.lookup k m))
               in view replaceable v

-- | Modify the post-delta value while leaving the original value unchanged.
--   To change the original AND the delta, use 'Map.alter' with a 
--   @ReplaceableMaybe a -> ReplaceableMaybe a@
adjust :: (Ord k, Patchable a, ValDeltaBundle a) =>
  (a -> a) -> k -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
adjust f k m = let (ReplaceableMaybe v) = fromMaybeCRM (Map.lookup k m)
                 in Map.insert k (ReplaceableMaybe $ (over replaceable (fmap f) v)) m
             
delete :: (Ord k, ValDeltaBundle a) =>
  k -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
delete k m =
    case (Map.lookup k m) of
        Nothing -> m
        Just (ReplaceableMaybe v) ->
            let v' = case v of
                        (ReplaceableValDelta vd) -> let (a,_) = unbundleVD vd
                                                    in ReplaceableValues a Nothing
                        (ReplaceableValues a _) -> ReplaceableValues a Nothing
            in
              Map.insert k (ReplaceableMaybe v') m

update :: (Ord k, ValDeltaBundle a, Patchable a, Eq a, Eq (ValDelta a)) =>
  (a -> Maybe a) -> k -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
update f k m = alterRM f' k m
    where f' Nothing = Nothing
          f' (Just x) = f x

alter :: (Ord k, ValDeltaBundle a, Patchable a, Eq a, Eq (ValDelta a)) =>
  (Maybe a -> Maybe a) -> k -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
alter f k m = Map.alter f' k m
    where f' = toMaybeCRM . (over replaceableMaybe f) . fromMaybeCRM

