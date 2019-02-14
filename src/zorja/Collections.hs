{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module Zorja.Collections (
      PatchableSet (..)
    , empty
    , insert
    , delete
    , member
    , add
    , remove
    )
    where

import GHC.Generics

import Zorja.Patchable
import Zorja.Jet

import Data.Set (Set)
import qualified Data.Set as Set


newtype PatchableSet a = PatchableSet (Set a) deriving (Eq, Generic, Show)

instance (Ord a) => Semigroup (PatchableSet a) where
    PatchableSet a <> PatchableSet b = PatchableSet (a <> b)

instance (Ord a) => Monoid (PatchableSet a) where
    mempty = PatchableSet Set.empty
    mappend = (<>)
--
-- inserts and deletes should be disjoint
--

data PatchableSetChanges a = PSChanges {
      inserts :: Set a
    , deletes :: Set a
    } deriving (Eq, Show)

instance (Ord a) => Semigroup (PatchableSetChanges a) where
    a <> b =  let ia = inserts a
                  da = deletes a
                  ib = inserts b
                  db = deletes b
              in
                  --
                  -- patch a (da <> db) = patch (patch a da) db
                  --
                  PSChanges ((Set.difference ia db) `Set.union` ib)
                            ((Set.difference da ib) `Set.union` db)

instance (Ord a) => Monoid (PatchableSetChanges a) where
    mempty = PSChanges Set.empty Set.empty
    mappend = (<>)

type instance (PatchDelta (PatchableSet a)) = PatchableSetChanges a

instance (Ord a) => Patchable (PatchableSet a) where
    patch (PatchableSet a) da = PatchableSet $
        a `Set.union` (inserts da) `Set.difference` (deletes da)
    changes (PatchableSet a) (PatchableSet b) = 
        let inserts' = Set.difference b a
            deletes' = Set.difference a b
        in PSChanges inserts' deletes'

empty :: (PatchableSet a)
empty = (PatchableSet Set.empty)

--
-- general destructuring op on PatchedJet (PatchableSet a)
goPJSet :: PatchedJet (PatchableSet a) 
        -> (Set a -> Set a)
        -> (Set a -> Set a)
        -> (Set a -> Set a)
        -> PatchedJet (PatchableSet a)
goPJSet pj f1 f2 f3 = 
    let (PatchableSet x) = (patchedval pj)
        x' = PatchableSet (f1 x)
        dx = history pj
        --
        -- inserts and deletes must be disjoint, so if we add @a@ to
        -- the @inserts@ field we must make sure it isn't in the @deletes@
        -- field
        dx' = PSChanges (f2 (inserts dx))
                        (f3 (deletes dx))
    in PatchedJet x' dx'


insert :: (Ord a) => a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
insert a pj = let ia = Set.insert a
                  da = Set.delete a
              in goPJSet pj ia ia da

delete :: (Ord a) => a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
delete a pj = let ia = Set.insert a
                  da = Set.delete a
              in goPJSet pj da da ia

member :: (Ord a) => a -> PatchedJet (PatchableSet a) -> Bool
member a pj = let (PatchableSet x) = patchedval pj
              in Set.member a x
--
-- Applying a union of two PatchedJet values is somewhat confusing, since
-- it's unclear how to merges the two patch histories. So instead a union-like
-- operation is provided, where it's basically equivalent to a bunch of inserts.
--
add :: (Ord a) => Set a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
add a pj =  let ia = Set.union a
                da = flip Set.difference a
            in goPJSet pj ia ia da

remove :: (Ord a) => Set a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
remove a pj =   let ia = Set.union a
                    da = flip Set.difference a
                in goPJSet pj da da ia

