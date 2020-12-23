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
    , UpDownSet (..)
    , ValDeltaSet (..)
    , empty
    , insert
    , delete
    , member
    , union
    , intersection
    , difference
    )
    where

import GHC.Generics

import Zorja.Patchable
import Zorja.Primitives

import Data.Set (Set)
import qualified Data.Set as Set


newtype PatchableSet a = PatchableSet (Set a)
    deriving (Eq, Generic, Show)

instance (Ord a) => Semigroup (PatchableSet a) where
    PatchableSet a <> PatchableSet b = PatchableSet (a <> b)

instance (Ord a) => Monoid (PatchableSet a) where
    mempty = PatchableSet Set.empty
    mappend = (<>)

instance Foldable PatchableSet where
    foldMap fm (PatchableSet a) = foldMap fm a

--
-- | A set that describes inserts and deletes in no particular
-- order. Inserts and deletes should be disjoint
--  There is no 'Semigroup' or 'Monoid' instance since I'm sure how to
--  to define it without accessing the original value.
--
data UpDownSet a = UpDownSet {
      inserts :: Set a
    , deletes :: Set a
    } deriving (Eq, Show, Generic)

instance (Ord a) => PatchInstance (UpDownSet a) where
    (UpDownSet i0 d0) <^< (UpDownSet i1 d1) = 
                  --
                  -- patch a (da <> db) = patch (patch a da) db
                  --
                  -- Start with patch a and apply patch b.
                  -- Items in b take precedence
        UpDownSet ((Set.difference i0 d1) `Set.union` i1)
                  ((Set.difference d0 i1) `Set.union` d1)

    noPatch = UpDownSet (Set.empty) (Set.empty)

upDownInsert :: (Ord a) => a -> UpDownSet a -> UpDownSet a
upDownInsert a (UpDownSet ia da) = UpDownSet (Set.insert a ia) (Set.delete a da)

upDownDelete :: (Ord a) => a -> UpDownSet a -> UpDownSet a
upDownDelete a (UpDownSet ia da) = UpDownSet (Set.delete a ia) (Set.insert a da)





data ValDeltaSet a = ValDeltaSet (PatchableSet a) (UpDownSet a)

type instance (ILCDelta (PatchableSet a)) = UpDownSet a
type instance (ValDelta (PatchableSet a)) = ValDeltaSet a

instance (Ord a, PatchInstance (UpDownSet a)) => Patchable (PatchableSet a) where
    patch (PatchableSet a) da = PatchableSet $
        a `Set.union` (inserts da) `Set.difference` (deletes da)
    changes (PatchableSet a) (PatchableSet b) = 
        let inserts' = Set.difference b a
            deletes' = Set.difference a b
        in UpDownSet inserts' deletes'

empty :: (ValDeltaSet a)
empty = ValDeltaSet (PatchableSet Set.empty) (UpDownSet (Set.empty) (Set.empty))

insert :: (Ord a) => a -> ValDeltaSet a -> ValDeltaSet a
insert a (ValDeltaSet s u) = ValDeltaSet s (upDownInsert a u)

delete :: (Ord a) => a -> ValDeltaSet a -> ValDeltaSet a
delete a (ValDeltaSet s u) = ValDeltaSet s (upDownDelete a u)

member :: (Ord a) => a -> ValDeltaSet a -> Bool
member a (ValDeltaSet (PatchableSet s) (UpDownSet i d)) =
    -- true IF:
    --  1. a is a member of the inserted values
    (Set.member a i) ||
    --  2. a is in the original set and hasn't been deleted
    ((Set.member a s) && not (Set.member a d))
              
--
-- Applying a union of two PatchedJet values is somewhat confusing, since
-- it's unclear how to merge the two patch histories. So instead a union-like
-- operation is provided, where it's basically equivalent to a bunch of inserts.
--

--
-- for union add all of a to the inserts, and remove any items in a from the
-- deletes
--
union :: (Ord a) => Set a -> ValDeltaSet a -> ValDeltaSet a
union a (ValDeltaSet (PatchableSet s) (UpDownSet i d)) =
    let i' = i `Set.union` a `Set.difference` s
        d' = d `Set.difference` a
    in
        ValDeltaSet (PatchableSet s) (UpDownSet i' d')

difference :: (Ord a) => Set a -> ValDeltaSet a -> ValDeltaSet a
difference a (ValDeltaSet (PatchableSet s) (UpDownSet i d)) =
    let i' = i `Set.difference` a
        d' = d `Set.union` a
    in
        ValDeltaSet (PatchableSet s) (UpDownSet i' d')

intersection :: (Ord a) => Set a -> ValDeltaSet a -> ValDeltaSet a
intersection a x@(ValDeltaSet (PatchableSet s) (UpDownSet i d)) =
    let d' = (Set.union s i) `Set.difference` a
    in difference d' x
