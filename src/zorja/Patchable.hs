{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Patchable (
    Patchable,
    patch,
    changes, 
    PatchInstance,
    mergePatches,
    (<^<),
    noPatch,
    ILCDelta,
    SelfDelta,
    valueToDelta,
    deltaToValue,
    SelfPatchable(..),
    patchGeneric, 
    changesGeneric
    )
    where

import GHC.Generics

import Data.Group

import Control.Applicative

-- | For a type @a@ there is a delta @ILCDelta a@ that describes how to
--  make changes to @a@ and produce a new value: @patch a (ILCDelta a) = a'@
--  ILC in this case is "Incremental Lambda Calculus"
type family ILCDelta a

-- | unit is it's own ILC delta
type instance (ILCDelta ()) = ()

-- | Class for combining 'ILCDelta' values.
-- Two patches can be combined. If we have two patches @da@ and @da'@ then
-- they can be combined into one patch @da <^< da'@, such that:
-- @patch a (da <^< da') = patch (patch a da) da'@.
-- This is distinct from 'Monoid' since merging patches might be different
-- than 'mappend'
--
class PatchInstance a where
    (<^<) :: a -> a -> a
    noPatch :: a

mergePatches :: (PatchInstance a) => a -> a -> a
mergePatches = (<^<)

-- |'Patchable' is a typeclass for data that can be diff'd and patched.
--  The associated type @ILCDelta a@ must be a 'PatchInstance' since it
--  can be combined with other changes to generate a "combined patch"
--  and must support an empty patch. Note that even though 'PatchInstance'
--  is a 'Monoid' that combines small
--  patches into a single bigger patch, it may have different behavior than
--  some default 'Monoid' instance for that type. You may have to use a newtype
--  wrapper to distinguish the two.
-- 
--  @patch x (changes x x') = x'@
class (PatchInstance (ILCDelta a)) => Patchable a where
  -- | @patch x dx@ applies the changes in @dx@ to @x@
  patch :: a -> ILCDelta a -> a
  -- | @changes x x'@ generates a @dx :: ILCDelta a@ that can convert @x@ into @x'@ using @patch@
  changes ::  a -> a -> ILCDelta a



-- | Some data types are their own delta. We can mark this with a typeclass.
--   See also @SelfPatchable@ which converts any @Group@ into a @SelfDelta@
class (Patchable a) => SelfDelta a where
  valueToDelta :: a -> ILCDelta a
  deltaToValue :: ILCDelta a -> a


--
-- | Patchable instance for functions
--

type instance ILCDelta (a -> b) = a -> ILCDelta a -> ILCDelta b

instance (PatchInstance b) => PatchInstance (a -> b) where
    ev <^< ev' = \a -> let a1 = ev  a
                           a2 = ev' a
                       in (a1 <^< a2)
    noPatch = \_ -> noPatch

instance (Patchable a, Patchable b) => Patchable (a -> b) where
    patch f ev = \a -> patch (f a) (ev a noPatch)
    changes f1 f2 = \a -> \da ->
        --
        -- Incorporate both f' and delta-f:
        --
        -- f' uses the change da:
        --   b1' = (f1 a) + (f1' a da)
        --
        -- delta-f doesn't handle the change da. Instead it is the change between f1
        -- and f2 when they are given the same argument value:
        --   "delta-f at a" = changes (f1 a) (f2 a)
        --   "delta-f at a'" = changes (f1 a') (f2 a')
        -- Note that delta-f may be different at different values of a
        -- 
        -- 
        let b1  = f1 a
            a' = patch a da
            --b1' = f1 a'           -- this represents (f1 a) + (f1' a da)
            b2' = f2 a'             -- delta-f from f1 to f2 at a':
                                    -- changes (f1 a) (f2 a) is delta-f at a
                                    -- changes (f1 a') (f2 a') is delta-f at a'
        in
            -- (changes b2' b1') <> (changes b1' b1) = changes b2' b1
            changes b2' b1

--
-- | Patchable tuples. In this case we just patch
--   each component independently, which may not be what
--   you want.
--

type instance ILCDelta (a,b) = (ILCDelta a, ILCDelta b)

instance (PatchInstance a, PatchInstance b) => PatchInstance (a,b) where
    (da,db) <^< (da',db') = (da <^< da', db <^< db')
    noPatch = (noPatch, noPatch)

instance (Patchable a, Patchable b) => Patchable (a,b) where
    patch (a,b) (da,db) = (patch a da, patch b db)
    changes (a0,b0) (a1,b1) = (changes a0 a1, changes b0 b1)
  

--
-- | If a is a group, we can generate a Patchable type where the 
--   delta is the same type as the actual value.
--   Patches are performed using semigroup (<>).
--   Works for some numbers (Integer) but for others you
--   have the problem that some values are unrepresentable.  For instance,
--   (changes a a') on float may produce a delta that is too small to
--   represent as a float.
--
--   We need @a@ to be a group since computing @changes@ requires the inverse of @a@
--

data SelfPatchable a = SelfPatchable a deriving (Eq, Show)


type instance ILCDelta (SelfPatchable a) = SelfPatchable a

instance (Group a, PatchInstance a) => SelfDelta (SelfPatchable a) where
    valueToDelta a = a
    deltaToValue da = da
    
instance Functor SelfPatchable where
    fmap f (SelfPatchable x) = SelfPatchable (f x)

instance Applicative (SelfPatchable) where
    pure x = SelfPatchable x
    (SelfPatchable a) <*> (SelfPatchable b) = SelfPatchable (a b)

instance (Semigroup a) => Semigroup (SelfPatchable a) where
    (SelfPatchable a) <> (SelfPatchable b) = SelfPatchable (a <> b)

instance (Monoid a) => Monoid (SelfPatchable a) where
    mempty = SelfPatchable mempty

instance (Num a) => Num (SelfPatchable a) where
    a + b = liftA2 (+) a b
    a * b = liftA2 (*) a b
    abs a = fmap abs a
    signum a = fmap signum a
    negate a = fmap negate a
    fromInteger n = SelfPatchable (fromInteger n)

instance (PatchInstance a) => PatchInstance (SelfPatchable a) where
    (SelfPatchable a) <^< (SelfPatchable b) = SelfPatchable (a <^< b)
    noPatch = SelfPatchable noPatch

instance (Group a, PatchInstance a) => Patchable (SelfPatchable a) where
    patch (SelfPatchable a) (SelfPatchable da) = SelfPatchable (a <> da)
    changes (SelfPatchable a) (SelfPatchable b) = SelfPatchable ((invert a) <> b)

instance (Ord a) => Ord (SelfPatchable a) where
    (SelfPatchable a) <= (SelfPatchable b) = a <= b


-- | Patchable generics, useful for records or extended sum types
--
class PatchG i o where
  patchG :: i p -> o p -> i p
  changesG :: i p -> i p -> o p

instance (Patchable x, dx ~ ILCDelta x) => PatchG (K1 a x) (K1 a dx) where
  patchG :: K1 a x p -> K1 a (ILCDelta x) p -> K1 a x p
  patchG (K1 x) (K1 dx) = K1 $ patch x dx
  changesG :: K1 a x p -> K1 a x p -> K1 a (ILCDelta x) p
  changesG (K1 x0) (K1 x1) = K1 $ changes x0 x1
  

instance (PatchG i o, PatchG i' o') => PatchG (i :*: i') (o :*: o') where
  patchG (l0 :*: r0) (l1 :*: r1) = (patchG l0 l1) :*: (patchG r0 r1)
  changesG (l0 :*: r0) (l1 :*: r1) = (changesG l0 l1) :*: (changesG r0 r1)

--
-- patch for a sum type allow patching a current value (left choices),
-- or switching to a separate value (right choices)
--
-- this means the change type for (A | B) would be:
--   (A :+: B :+: (ILCDelta (A | B)))
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
-- ILCDelta for generics
--



patchGeneric ::
  (Generic f,
   Generic (ILCDelta f),
--    Monoid (ILCDelta f),
   PatchG (Rep f) (Rep (ILCDelta f)))
  => f -> (ILCDelta f) -> f
patchGeneric a da = to $ patchG (from a) (from da)

changesGeneric ::
  (Generic f,
   Generic (ILCDelta f),
   PatchG (Rep f) (Rep (ILCDelta f)))
  => f -> f -> (ILCDelta f)
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

