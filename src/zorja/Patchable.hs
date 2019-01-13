{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module Zorja.Patchable where

import GHC.Generics

import Data.Text
import Data.Semigroup

--import Data.Semigroup
--import Data.Monoid

import Control.Lens hiding (from, to)
--import Control.Lens.Tuple

type family PatchDelta a

-- |
-- | A typeclass for data that can be diff'd and patched.
-- | The associated type @Change a@ must be a Monoid since it
-- | can be combined with other changes to generate a "combined patch"
-- | and must support an empty patch.
-- |
-- | @patch a (changes a b) = b@

class (Monoid (PatchDelta a)) => Patchable a where
  -- @patch a da@ applies the changes in @da@ to @a@
  patch :: a -> PatchDelta a -> a
  -- @changes a b@ generates a @Change a@ that can convert a into b via @patch@
  changes ::  a -> a -> PatchDelta a


--
-- patchable instance for Text
--

type instance PatchDelta Text = Option (Last Text)

instance Patchable Text where
  patch x dx = case getOption dx of
    Nothing -> x
    Just dx' -> getLast dx'
  changes x0 x1 = if x0 == x1
                  then Option Nothing
                  else Option (Just (Last x1))

--
-- AtomicLast is a Patchable type that just replaces the
-- previous value. Efficient for primitive types, but
-- larger data structures should use something more clever
--

newtype AtomicLast a = AtomicLast a deriving (Eq, Show)

type instance PatchDelta (AtomicLast a) = (Option (Last a))

instance (Eq a) => Patchable (AtomicLast a) where
  patch a da = case getOption da of
                 Nothing -> a
                 Just (Last a') -> AtomicLast a'
  changes (AtomicLast a) (AtomicLast b) =
    if (a == b)
    then Option Nothing
    else Option $ Just (Last b)

--
-- Patchable Pair
--

data Pair a = Ax a a deriving (Eq, Show, Generic)


instance (Semigroup a) => Semigroup (Pair a) where
  (Ax a b) <> (Ax a' b') = Ax (a <> a') (b <> b')
  
instance (Monoid a) => Monoid (Pair a) where
  mempty = Ax mempty mempty
  mappend = (<>)

type instance PatchDelta (Pair a) = Option (Last (Pair a))

instance (Eq a) => Patchable (Pair a) where
  patch x dx = case getOption dx of
    Nothing -> x
    Just dx' -> getLast dx'
  changes x0 x1 = if x0 == x1
                  then Option Nothing
                  else Option (Just (Last x1))
                          



--
-- @Jet@ bundles a value and its delta into a single record.
--

data Jet a = Jet
  {
    position :: a, 
    velocity :: PatchDelta a
  }

toJet :: (Patchable a) => a -> Jet a
toJet x = Jet { position = x, velocity = mempty }


deriving instance (Eq a, Eq (PatchDelta a), Patchable a) => Eq (Jet a)
deriving instance (Show a, Show (PatchDelta a), Patchable a) => Show (Jet a)



-- A PatchedJet contains patch data and the value AFTER the
-- patch has been applied. This is useful when compose functions
-- that produce and accumulate patch data. Otherwise when composing
-- we have to always apply 'patch a da' to get the most up-to-date
-- changed value.

data PatchedJet a = PatchedJet { patchedval :: a, history :: PatchDelta a }
                  deriving (Generic)

deriving instance (Eq a, Eq (PatchDelta a), Patchable a) => Eq (PatchedJet a)
deriving instance (Show a, Show (PatchDelta a), Patchable a) => Show (PatchedJet a)

toPatchedJet :: (Patchable a) => a -> PatchedJet a
toPatchedJet a = PatchedJet a mempty


--
-- PatchedJet lenses for  tuples
--

type instance PatchDelta (a,b) = (PatchDelta a, PatchDelta b)

instance (Patchable a, Patchable b) => Patchable (a,b) where
  patch (a,b) (da,db) = (patch a da, patch b db)
  changes (a0,b0) (a1,b1) = (changes a0 a1, changes b0 b1)

instance 
  Field1 (PatchedJet (a,b)) (PatchedJet (a,b)) (PatchedJet a) (PatchedJet a)
    where
  _1 k (PatchedJet (a,b) (da,db)) = 
    let x' = k (PatchedJet a da)
        lxify = \(PatchedJet a' da') -> PatchedJet (a',b) (da', db)
    in fmap lxify x'
  

instance 
  Field2 (PatchedJet (a,b)) (PatchedJet (a,b)) (PatchedJet b) (PatchedJet b)
    where
  _2 k (PatchedJet (a,b) (da,db)) = 
    let bX = k (PatchedJet b db)
        lxify = \(PatchedJet b' db') -> PatchedJet (a,b') (da, db')
    in fmap lxify bX


--
-- Patchable generics, useful for records or extended sum types
--



class PatchG i o where
  patchG :: i p -> o p -> i p
  changesG :: i p -> i p -> o p

instance (Patchable x, dx ~ PatchDelta x) => PatchG (K1 a x) (K1 a dx) where
  patchG :: K1 a x p -> K1 a (PatchDelta x) p -> K1 a x p
  patchG (K1 x) (K1 dx) = K1 $ patch x dx
  changesG :: K1 a x p -> K1 a x p -> K1 a (PatchDelta x) p
  changesG (K1 x0) (K1 x1) = K1 $ changes x0 x1
  

instance (PatchG i o, PatchG i' o') => PatchG (i :*: i') (o :*: o') where
  patchG (l0 :*: r0) (l1 :*: r1) = (patchG l0 l1) :*: (patchG r0 r1)
  changesG (l0 :*: r0) (l1 :*: r1) = (changesG l0 l1) :*: (changesG r0 r1)

--
-- patch for a sum type allow patching a current value (left choices),
-- or switching to a separate value (right choices)
--
-- this means the change type for (A | B) would be:
--   (A :+: B :+: (PatchDelta (A | B)))
--

instance (PatchG i o, PatchG i' o')
    => PatchG (i :+: i') (i :+: i' :+: o :+: o') where
  patchG (L1 a) (R1 (R1 (L1 da))) = L1 $ patchG a da
  patchG _ (R1 (L1 b))  = R1 $ b
  patchG (R1 b) (R1 (R1 (R1 db))) = R1 $ patchG b db
  patchG _ (L1 a)  = L1 $ a
  -- these should not occur, sigh
  patchG (L1 _) (R1 (R1 (R1 _))) = undefined
  patchG (R1 _) (R1 (R1 (L1 _))) = undefined

  
  changesG (L1 a) (L1 a') = R1 . R1 . L1 $ changesG a a'
  changesG (L1 _) (R1 b)  = R1 . L1 $ b
  changesG (R1 _) (L1 a)  = L1 $ a
  changesG (R1 b) (R1 b') = R1 . R1 . R1  $ changesG b b'

instance (PatchG i o) => PatchG (M1 _a _b i) (M1 _a' _b' o) where
  patchG   (M1 x) (M1 dx) = M1 $ patchG x dx
  changesG (M1 x) (M1 y)  = M1 $ changesG x y


instance PatchG V1 V1 where
  patchG   = undefined
  changesG = undefined

instance PatchG U1 U1 where
  patchG U1 U1   = U1
  changesG U1 U1 = U1

--
-- PatchDelta for generics
--



patchGeneric ::
  (Generic f,
   Generic (PatchDelta f),
--    Monoid (PatchDelta f),
   PatchG (Rep f) (Rep (PatchDelta f)))
  => f -> (PatchDelta f) -> f
patchGeneric a da = to $ patchG (from a) (from da)

changesGeneric ::
  (Generic f,
   Generic (PatchDelta f),
   PatchG (Rep f) (Rep (PatchDelta f)))
  => f -> f -> (PatchDelta f)
changesGeneric a b = to $ changesG (from a) (from b)  
  
--  patch a da = to $ patchG (from a) (from da)
--  changes a a' = to $ changesG (from a) (from a')
