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

module Zorja.Patchable 
    (Patchable,
    patch,
    changes, 
    PatchDelta, 
    AtomicLast(..),
    ANum(..), 
    DNum(..),
    patchGeneric, 
    changesGeneric)
    where

import GHC.Generics

import Data.Text
import Data.Semigroup
--import Data.Maybe

--import Data.Semigroup
--import Data.Monoid
import Control.Applicative

--import Control.Lens.Tuple

type family PatchDelta a

-- unit has no delta
type instance (PatchDelta ()) = ()

-- |
-- | A typeclass for data that can be diff'd and patched.
-- | The associated type @PatchDelta a@ must be a Monoid since it
-- | can be combined with other changes to generate a "combined patch"
-- | and must support an empty patch.
-- |
-- | @patch a (changes a b) = b@

class (Monoid (PatchDelta a)) => Patchable a where
  -- @patch a da@ applies the changes in @da@ to @a@
  patch :: a -> PatchDelta a -> a
  -- @changes a b@ generates a @Change a@ that can convert a into b via @patch@
  changes ::  a -> a -> PatchDelta a

-- |
-- | AtomicLast is a Patchable type that just replaces the
-- | previous value. Efficient for primitive types, but
-- | larger data structures should use something more clever
-- |
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

instance Functor AtomicLast where
  fmap f (AtomicLast x) = AtomicLast (f x)

instance Applicative AtomicLast where
  pure x = AtomicLast x
  (AtomicLast a) <*> (AtomicLast b) = AtomicLast (a b)


  
--
-- Patchable instance for functions
--

type instance PatchDelta (a -> b) = a -> PatchDelta a -> PatchDelta b

instance (Patchable a, Patchable b) => Patchable (a -> b) where
    patch f ev = \a -> patch (f a) (ev a mempty)
    changes f1 f2 = \a -> \da ->
        -- incorporate both f' and delta-f
        let b1  = f1 a
            b1' = f1 (patch a da)   -- changes b1' b1  is f'
            b2' = f2 (patch a da)   -- changes b2' b1' is delta-f (patch a da)
         in
            changes b2' b1

{- type instance PatchDelta ((->) a b) = (a -> b) -> (a -> b)


instance (Monoid b, Patchable b) => Patchable ((->) a b) where
    patch f df = df f
    changes f f' = \xf -> 
                        -- we don't know what's in xf, so instead of patching
                        -- xf directly we patch the return value of xf
                        \a -> let x = xf a
                                  b = f a
                                  b' = f' a
                              in patch x ((changes x b) <> (changes b b'))
-}
--
-- Patchable Pair
--

data Pair a = Ax a a deriving (Eq, Show, Generic)


instance (Semigroup a) => Semigroup (Pair a) where
  (Ax a b) <> (Ax a' b') = Ax (a <> a') (b <> b')
  
instance (Monoid a) => Monoid (Pair a) where
  mempty = Ax mempty mempty

type instance PatchDelta (Pair a) = Option (Last (Pair a))

instance (Eq a) => Patchable (Pair a) where
  patch x dx = case getOption dx of
    Nothing -> x
    Just dx' -> getLast dx'
  changes x0 x1 = if x0 == x1
                  then Option Nothing
                  else Option (Just (Last x1))
                          
--
-- | Patchable tuples. In this case we just patch
-- | each component independently, which may not be what
-- | you want.
--

type instance PatchDelta (a,b) = (PatchDelta a, PatchDelta b)

instance (Patchable a, Patchable b) => Patchable (a,b) where
  patch (a,b) (da,db) = (patch a da, patch b db)
  changes (a0,b0) (a1,b1) = (changes a0 a1, changes b0 b1)
  

-- |
-- | Patchable instance for Text, basically works as AtomicLast
-- |

type instance PatchDelta Text = Option (Last Text)

instance Patchable Text where
  patch x dx = case getOption dx of
    Nothing -> x
    Just dx' -> getLast dx'
  changes x0 x1 = if x0 == x1
                  then Option Nothing
                  else Option (Just (Last x1))

--
-- | 'Atomic Num' basically a Num type that supports AtomicLast
-- | style patching.
--

newtype ANum a = ANum a deriving (Eq, Show)

type instance PatchDelta (ANum a) = Option (Last a)

instance Functor ANum where
  fmap f (ANum x) = ANum (f x)

instance Applicative (ANum) where
  pure x = ANum x
  (ANum a) <*> (ANum b) = ANum (a b)

instance (Num a) => Num (ANum a) where
  a + b = liftA2 (+) a b
  a * b = liftA2 (*) a b
  abs a = fmap abs a
  signum a = fmap signum a
  negate a = fmap negate a
  fromInteger n = ANum (fromInteger n)

instance (Eq a) => Patchable (ANum a) where
  patch x dx = case getOption dx of
    Nothing -> x
    Just dx' -> ANum (getLast dx')
  changes (ANum x0) (ANum x1) =
      if x0 == x1
      then Option Nothing
      else Option (Just (Last x1))

instance (Ord a) => Ord (ANum a) where
    (ANum a) <= (ANum b) = a <= b

--
-- Patchable type where the delta is the same type as the
-- actual value. Works for some numbers (Integer) but for others you
-- have the problem that some values are unrepresentable.  For instance,
-- (changes a a') on float may produce a delta that is too small to
-- represent as a float.
--
--

newtype DNum a = DNum a deriving (Eq, Show)

type instance PatchDelta (DNum a) = DNum a

instance Functor DNum where
    fmap f (DNum x) = DNum (f x)

instance Applicative (DNum) where
    pure x = DNum x
    (DNum a) <*> (DNum b) = DNum (a b)

instance (Num a) => Semigroup (DNum a) where
    (DNum a) <> (DNum b) = DNum (a + b)

instance (Num a) => Monoid (DNum a) where
    mempty = DNum 0

instance (Num a) => Num (DNum a) where
    a + b = liftA2 (+) a b
    a * b = liftA2 (*) a b
    abs a = fmap abs a
    signum a = fmap signum a
    negate a = fmap negate a
    fromInteger n = DNum (fromInteger n)

instance (Num a, Monoid (DNum a)) => Patchable (DNum a) where
    patch (DNum a) (DNum da) = DNum (a + da)
    changes (DNum a) (DNum b) = DNum (b - a)

instance (Ord a) => Ord (DNum a) where
    (DNum a) <= (DNum b) = a <= b


--
-- patchable lists
--

data ListDelta a = PatchNode (PatchDelta a) (ListDelta a)
                 | KeepList

type instance (PatchDelta [a]) = ListDelta a

instance (Patchable a) => Semigroup (ListDelta a) where
    a <> KeepList = a
    KeepList <> a = a
    (PatchNode a as) <> (PatchNode a' as') = PatchNode (a <> a') (as <> as')

instance (Patchable a) => Monoid (ListDelta a) where
    mempty = KeepList

instance (Patchable a) => Patchable [a] where
    patch x KeepList = x
    patch (x:xs) (PatchNode da das) = (patch x da) : patch xs das
    patch [] (PatchNode _ _) = undefined   -- can't patch empty node!
    patch (x:xs) (PatchNode a as) = (patch x a) : patch xs as
    changes x x' = undefined

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


--
-- The patchable for a sum type @a@ has two constructors:
--  - NewSum @a@ replaces the current val with the new value @a@. For
--        a sum type this is how you switch to a different constructor
--  - PatchSum @da@ applies the patch @da@ to the current value. The type
--        of @da@ is the Patchable of the constructor of the current value.
--

