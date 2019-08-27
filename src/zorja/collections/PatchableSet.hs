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


module Zorja.Collections.PatchableSet (
      PatchableSet (..)
    , empty
    , insert
    , delete
    , member
    , union
    , intersection
    , difference
    , inserts
    , deletes
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

instance Foldable PatchableSet where
    foldMap fm (PatchableSet a) = foldMap fm a

--
-- A set that describes inserts and deletes in no particular
-- order. Inserts and deletes should be disjoint
--

data UpDownSet a = UpDownSet {
      inserts :: Set a
    , deletes :: Set a
    } deriving (Eq, Show)

instance (Ord a) => Semigroup (UpDownSet a) where
    a <> b =  let ia = inserts a
                  da = deletes a
                  ib = inserts b
                  db = deletes b
              in
                  --
                  -- patch a (da <> db) = patch (patch a da) db
                  --
                  UpDownSet ((Set.difference ia db) `Set.union` ib)
                            ((Set.difference da ib) `Set.union` db)

instance (Ord a) => Monoid (UpDownSet a) where
    mempty = UpDownSet Set.empty Set.empty
    mappend = (<>)

type instance (PatchDelta (PatchableSet a)) = UpDownSet a

instance (Ord a) => Patchable (PatchableSet a) where
    patch (PatchableSet a) da = PatchableSet $
        a `Set.union` (inserts da) `Set.difference` (deletes da)
    changes (PatchableSet a) (PatchableSet b) = 
        let inserts' = Set.difference b a
            deletes' = Set.difference a b
        in UpDownSet inserts' deletes'

empty :: (PatchableSet a)
empty = (PatchableSet Set.empty)

--
-- general destructuring op on PatchedJet (PatchableSet a)
--
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
        dx' = UpDownSet (f2 (inserts dx))
                        (f3 (deletes dx))
    in
        PatchedJet x' dx'


insert :: (Ord a) => a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
insert a pj = let ia = Set.insert a
                  da = Set.delete a
              in
                  goPJSet pj ia ia da

delete :: (Ord a) => a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
delete a pj = let ia = Set.insert a
                  da = Set.delete a
              in
                  goPJSet pj da da ia

member :: (Ord a) => a -> PatchedJet (PatchableSet a) -> Bool
member a pj = let (PatchableSet x) = patchedval pj
              in
                  Set.member a x
              
--
-- Applying a union of two PatchedJet values is somewhat confusing, since
-- it's unclear how to merge the two patch histories. So instead a union-like
-- operation is provided, where it's basically equivalent to a bunch of inserts.
--

--
-- for union add all of a to the inserts, and remove any items in a from the
-- deletes
--
union :: (Ord a) => Set a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
union a pj =  let ia = Set.union a
                  da = flip Set.difference a
              in goPJSet pj ia ia da

difference :: (Ord a) => Set a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
difference a pj =   let ia = Set.union a
                        da = flip Set.difference a
                    in goPJSet pj da da ia

intersection :: (Ord a) => Set a -> PatchedJet (PatchableSet a) -> PatchedJet (PatchableSet a)
intersection a pj = let (PatchableSet x) = (patchedval pj)
                        -- intersection removes elements of a that aren't in x
                        removes = Set.difference a x
                    in difference removes pj                
