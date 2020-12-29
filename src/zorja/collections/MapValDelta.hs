{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : Zorja.Collections.MapValDelta
Description : Handle a map of ReplaceableMaybe elements.
Copyright   : (c) Gary Haussmann, 2019
Stability   : experimental

The 'ValDelta' of a Map. For this we  have to mark insert and deletes as well just
straight patches to elements.

-}

module Zorja.Collections.MapValDelta
    (
        MapValues(..),
        MapDelta(..),
        MapValDelta(..),
        insert,
        lookup,
        adjust,
        delete,
        update,
        alter,
        keys,
        size
    ) where

import Prelude hiding (lookup)

import qualified Data.Map.Strict as M
import Data.Map.Merge.Strict (merge, mapMissing, zipWithMatched)

import Zorja.Patchable

data MapDeltaElement a =
    MapInsertElement a
  | MapDeleteElement a
  | MapPatchElement (ILCDelta a)

data MapValDeltaElement a =
    MapInsert a
  | MapDelete a
  | MapPatch (ValDelta a)

instance (Patchable a) => PatchInstance (MapDeltaElement a) where
    _                  <^< MapInsertElement a  = MapInsertElement a
    -- note that an insert followed by a delete will produce a delete delta, even though
    -- there was nothing here in the original map value. This effects how we bundle deletes
    _                  <^< MapDeleteElement a = MapDeleteElement a
    MapInsertElement a <^< MapPatchElement da  = MapInsertElement (patch (bundleVD (a,da)))
    MapPatchElement da <^< MapPatchElement db  = MapPatchElement (da <^< db)
    MapDeleteElement a <^< MapPatchElement _   = MapDeleteElement a

newtype MapValues k a = MapValues (M.Map k a)
    deriving (Eq, Show)

newtype MapDelta k a = MapDelta (M.Map k (MapDeltaElement a))

newtype MapValDelta k a = MapValDelta (M.Map k (MapValDeltaElement a))


instance (Show a, Show (ILCDelta a)) => Show (MapDeltaElement a) where
    show (MapInsertElement a) = "InsertElement " ++ show a
    show (MapPatchElement da) = "PatchElement " ++ show da
    show (MapDeleteElement a) = "DeleteElement " ++ show a

instance (Show a, Show (ValDelta a)) => Show (MapValDeltaElement a) where
    show (MapInsert aa) = "MapInsert " ++ show aa
    show (MapDelete aa) = "MapDelete " ++ show aa
    show (MapPatch aa)  = "MapPatch " ++ show aa

instance (Show k, Show a, Show (ILCDelta a)) => Show (MapDelta k a) where
    show (MapDelta dm) = "MapDelta " ++ show dm

instance (Show k, Show a, Show (ValDelta a)) => Show (MapValDelta k a) where
    show (MapValDelta mm) = "MapValDelta " ++ show mm

type instance ILCDelta (MapValues k a) = MapDelta k a
type instance ValDelta (MapValues k a) = MapValDelta k a

instance (Ord k, Patchable a, ValDeltaBundle a) => ValDeltaBundle (MapValues k a) where
    bundleVD (MapValues m, MapDelta dm) = MapValDelta $ M.mapMaybe id $
        merge (mapMissing onlyM1) (mapMissing onlyM2) (zipWithMatched inBoth) m dm
        where
            onlyM1 _ a = Just $ MapPatch (valueBundle a)
            onlyM2 _ (MapInsertElement x) = Just $MapInsert x
            onlyM2 _ (MapDeleteElement _) = Nothing
            onlyM2 _ (MapPatchElement _)  = error "Mismatch in MapElement bundle"
            inBoth _ a (MapInsertElement a') = Just $ MapPatch (diffBundle a a')
            inBoth _ a (MapPatchElement da)  = Just $ MapPatch (bundleVD (a,da))
            inBoth _ a (MapDeleteElement _) = Just $ MapDelete a
      
    unbundleVD (MapValDelta mm) =
        let (m,dm) = M.foldrWithKey split (M.empty, M.empty) mm
        in (MapValues m, MapDelta dm)
            where
                split k (MapInsert a) (m,dm) = (m, M.insert k (MapInsertElement a) dm)
                split k (MapDelete a) (m,dm) = (M.insert k a m, 
                                                M.insert k (MapDeleteElement a) dm)
                split k (MapPatch aa) (m,dm) =
                    let (a,da) = unbundleVD aa
                    in (M.insert k a m, M.insert k (MapPatchElement da) dm)

    valueBundle (MapValues m) = MapValDelta (M.map (\x -> MapPatch (valueBundle x)) m)

instance (Ord k, Patchable a) => PatchInstance (MapDelta k a) where
    (MapDelta dm) <^< (MapDelta dm') = MapDelta $
        merge (mapMissing onlyOne) (mapMissing onlyOne) (zipWithMatched inBoth) dm dm'
        where
            onlyOne _ a = a
            inBoth _ a a' = a <^< a'

instance (Ord k, Patchable a, PatchInstance (MapDelta k a )) => Patchable (MapValues k a) where
    patch (MapValDelta mm) = MapValues $ M.mapMaybe patchElement mm
        where
            patchElement (MapInsert a) = Just a
            patchElement (MapDelete _) = Nothing
            patchElement (MapPatch aa) = Just (patch aa)


    diffBundle (MapValues x) (MapValues x') = MapValDelta $
        merge (mapMissing onlyM1) (mapMissing onlyM2) (zipWithMatched inBoth) x x'
        where
            onlyM1 _ a = MapDelete a
            onlyM2 _ a = MapInsert a
            inBoth _ a a' = MapPatch (diffBundle a a')



insert :: (Ord k, Patchable a) => k -> a -> MapValDelta k a -> MapValDelta k a
insert k v (MapValDelta mm) = MapValDelta $ M.alter insertVD k mm
  where
    insertVD Nothing              = Just (MapInsert v)
    -- something already inserted, just replace it
    insertVD (Just (MapInsert _)) = Just (MapInsert v)
    -- something was deleted, add it back in via patch
    insertVD (Just (MapDelete x)) = let newValDelta = diffBundle x v
                                    in Just (MapPatch newValDelta)
    -- something patched, replace with new value
    insertVD (Just (MapPatch xx)) =
        let (x,_) = unbundleVD xx
            newValDelta = diffBundle x v
        in Just (MapPatch newValDelta)


delete :: (Ord k, Patchable a) => k -> MapValDelta k a -> MapValDelta k a
delete k (MapValDelta mm) = MapValDelta $ M.alter deleteVD k mm
    where
        deleteVD Nothing = Nothing
        deleteVD (Just (MapInsert _)) = Nothing
        deleteVD (Just (MapDelete x)) = Just (MapDelete x)
        deleteVD (Just (MapPatch xx)) =
            let (x,_) = unbundleVD xx
            in Just (MapDelete x)



-- | Lookup always pulls the value (or lack thereof) post-patch. So if an element
--   was deleted it will not show up in 'lookup'
lookup :: (Ord k, Patchable a) => k -> MapValDelta k a -> Maybe a
lookup k (MapValDelta mm) =
    case (M.lookup k mm) of
        Nothing -> Nothing
        Just (MapInsert a) -> Just a
        Just (MapDelete _) -> Nothing
        Just (MapPatch aa) -> Just (patch aa)


-- | Modify the post-delta value while leaving the original value unchanged.
--   To change the original AND the delta, use 'Map.alter' with a 
--   @ReplaceableMaybe a -> ReplaceableMaybe a@
adjust :: (Ord k, Patchable a) => (a -> a) -> k -> MapValDelta k a -> MapValDelta k a
adjust f k mm = alter (fmap f) k mm
             


update :: (Ord k, Patchable a) => (a -> Maybe a) -> k -> MapValDelta k a -> MapValDelta k a
update f k mm = alter updateVD k mm
    where
        updateVD Nothing = Nothing
        updateVD (Just x) = f x


alter :: (Ord k, Patchable a) => (Maybe a -> Maybe a) -> k -> MapValDelta k a -> MapValDelta k a
alter f k (MapValDelta mm) = MapValDelta (M.alter alterVD k mm)
    where
        alterVD Nothing = case (f Nothing) of
                              Nothing -> Nothing
                              Just x' -> Just (MapInsert x')
        alterVD (Just (MapInsert x)) = case (f (Just x)) of
                                           Nothing -> Nothing
                                           Just x' -> Just (MapInsert x')
        alterVD (Just (MapDelete x)) = Just (MapDelete x)
        alterVD (Just (MapPatch xx)) = case (f (Just (patch xx))) of
                                            Nothing -> Nothing
                                            Just x' -> let x = fst (unbundleVD xx)
                                                       in Just (MapPatch (diffBundle x x'))

keys :: MapValDelta k a -> [k]
keys (MapValDelta mm) = M.keys mm

size :: MapValDelta k a -> Int
size (MapValDelta mm) = M.size mm
