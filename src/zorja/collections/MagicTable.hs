{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

{-|
Module      : Zorja.Collections.MagicTable
Description : Sets where element equivalence (and ordering) is determined by
              computed "primary key" of the element.
Stability   : Experimental
-}

module Zorja.Collections.MagicTable where

import Data.Kind
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as M

import Zorja.Patchable
import Zorja.Primitives

newtype MagicTable a = MagicTable (IntMap a) deriving (Eq, Show)

class AsMagicTable p where
  type UpdateVal p a :: Type
  type ValueConstraint p a :: Constraint
  lookup :: (ValueConstraint p a) => Int -> p a -> Maybe a
  insert :: (ValueConstraint p a) => Int -> a -> p a -> p a
  delete :: (ValueConstraint p a) => Int -> p a -> p a
  update :: (ValueConstraint p a) => Int -> (UpdateVal p a -> Maybe (UpdateVal p a)) -> p a -> p a
  fromList :: (ValueConstraint p a) => ((UpdateVal p a) -> Int) -> [UpdateVal p a] -> p a
  mapMagic :: (ValueConstraint p a, ValueConstraint p b) => (UpdateVal p a -> UpdateVal p b) -> p a -> p b
  
instance AsMagicTable MagicTable where
  type UpdateVal MagicTable a = a
  type ValueConstraint MagicTable a = ()
  lookup k (MagicTable t) = M.lookup k t
  insert k v (MagicTable t) = MagicTable (M.insert k v t)
  delete k (MagicTable t) = MagicTable (M.delete k t)
  update k f (MagicTable t) = MagicTable (M.update f k t)
  fromList kf l = let
                    withKeys = fmap (\a -> (kf a, a)) l
                  in
                    MagicTable (M.fromList withKeys)
  mapMagic f (MagicTable t) = MagicTable (M.map f t)

instance Functor MagicTable where
  fmap f (MagicTable t) = MagicTable $ M.map f t

newtype MagicJetTable a = MagicJetTable (IntMap (AddRemoveOp a))

-- | To get the key from a MagicJetTable value we need to deconstruct the sum type
magicOpKey :: (ValDeltaBundle a) => (a -> Int) -> AddRemoveOp a -> Int
magicOpKey _  NullValueOp    = undefined
magicOpKey kf (AddValueOp a) = kf a
magicOpKey kf (RemoveValueOp a) = kf a
magicOpKey kf (PatchValueOp vda) = let (v, _dv) = unbundleVD vda in kf v

instance AsMagicTable MagicJetTable where
  type UpdateVal MagicJetTable a = ValDelta a
  type ValueConstraint MagicJetTable a = (ValDeltaBundle a, Patchable a)
  lookup k (MagicJetTable t) =
    -- the lookup result appears as the patched result, not the original values
    -- if you want access to the raw unpatched value use update
    case (M.lookup k t) of
      Nothing -> Nothing
      Just NullValueOp    -> Nothing
      Just (AddValueOp v) -> Just v
      Just (RemoveValueOp _) -> Nothing
      -- when pulling out data, we pull out the patched value not the pre-patched value
      Just (PatchValueOp j) -> Just (patchVD j)
  insert k v (MagicJetTable t) =
    let newvalue = case (M.lookup k t) of
                      Nothing -> AddValueOp v
                      Just NullValueOp    -> AddValueOp v
                      Just (AddValueOp _) -> AddValueOp v
                      Just (RemoveValueOp v')  -> PatchValueOp (bundleVD (v', changes v' v))
                      Just (PatchValueOp j)  -> let (a,da) = unbundleVD j
                                                    a' = patch a da
                                                    da' = changes a' v
                                                in PatchValueOp (bundleVD (a,da'))
    in
      MagicJetTable (M.insert k newvalue t)
  delete k (MagicJetTable t) =
    let newmap = case (M.lookup k t) of
          Nothing -> t
          Just NullValueOp -> t
          Just (AddValueOp _) -> M.delete k t
          Just (RemoveValueOp _) -> t
          Just (PatchValueOp j) -> M.insert k (RemoveValueOp (patchVD j)) t
    in
      MagicJetTable newmap
  update k f (MagicJetTable t) =
    case (M.lookup k t) of
      Nothing -> MagicJetTable t
      Just x  -> MagicJetTable $ M.insert k (updateOp f x) t
  fromList kf l = let
                    withKeys = fmap (\a -> (kf a, PatchValueOp a)) l
                  in
                    MagicJetTable (M.fromList withKeys)
  mapMagic f (MagicJetTable t) = MagicJetTable (M.map (mapOp f) t)


-- | Update a @MagicJetTable@ element, possibly deleting it.
updateOp :: (ValDeltaBundle a, Patchable a)
    => (ValDelta a -> Maybe (ValDelta a)) -> AddRemoveOp a -> AddRemoveOp a
updateOp _ NullValueOp    = NullValueOp
updateOp f (AddValueOp v) = case (f (bundleVD (v,noPatch))) of
                                  Nothing -> RemoveValueOp v
                                  Just x -> AddValueOp (patchVD x)
updateOp _ (RemoveValueOp v)  = RemoveValueOp v
updateOp f (PatchValueOp j)  = case (f j) of
                                  Nothing -> RemoveValueOp (patchVD j)
                                  Just x -> PatchValueOp x

-- | Apply a function to a @MagicJetTable@ element, with no deleting.
mapOp :: (ValDeltaBundle a, Patchable a, ValDeltaBundle b, Patchable b)
    => (ValDelta a -> ValDelta b) -> AddRemoveOp a -> AddRemoveOp b
mapOp _ NullValueOp    = NullValueOp
mapOp f (AddValueOp v) = AddValueOp (autoPatchFunction f v)
mapOp f (RemoveValueOp v)  = RemoveValueOp (autoPatchFunction f v)
mapOp f (PatchValueOp j)  = PatchValueOp (f j)
                              
