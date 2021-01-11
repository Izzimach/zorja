{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Primitives 
    (
        -- * A type where the delta simply replaces old values
        --
        -- $replaceOnly
        ReplaceOnly(..),
        Replacing(..),
        ReplaceValDelta(..),

        -- * A number where the delta is of the same numeric type
        --
        -- $diffNum
        DiffNum(..),
        DiffNumValDelta(..),

        SelfPatchable(..),
    )
    where

import Prelude

import qualified GHC.Generics as GHC
import Generics.SOP

import Control.Applicative
import Control.Lens.Wrapped

import Data.Functor.Identity
import Data.Group
import Data.Semigroup
import Data.Maybe

import Zorja.Patchable


-- $replaceOnly
--
-- The types 'ReplaceOnly' and 'Replacing' make up a type
-- where applying patches just replace the original value with a new value.
-- The result of merging two patches if to just take the most recent value
-- (the one on the right side of the (<^<) operator) just like @Option (Last a)@ would
-- do.


-- | ReplaceOnly is a 'Patchable' type that just replaces the
--  previous value. Efficient for primitive types like float and short text, but
--  larger data structures should use something more clever.
newtype ReplaceOnly a = ReplaceOnly a
    deriving (Eq, Show, GHC.Generic)
    deriving (Functor, Applicative) via Identity
    deriving (Semigroup, Monoid, Num, Ord) via a

-- | 'Replacing a' is the 'PatchDelta' of 'ReplaceOnly'. It 
--  behaves as 'Maybe a' when used as a 'Monoid'. However, it
--  behaves as 'Option (Last a)' when used as a 'PatchInstance'
newtype Replacing a = Replacing (Maybe a)
    deriving (Eq, Show, GHC.Generic)
    deriving (Functor, Applicative) via Maybe
    deriving (Semigroup, Monoid) via (Maybe a)

data ReplaceValDelta a = ReplaceValDelta a (Replacing a)
    deriving (Eq, Show, GHC.Generic)

type instance ILCDelta (ReplaceOnly a) = Replacing a
type instance ValDelta (ReplaceOnly a) = ReplaceValDelta a

instance Generic (ReplaceOnly a)
instance Generic (Replacing a)
instance Generic (ReplaceValDelta a)

instance Wrapped (ReplaceOnly a) where
    type Unwrapped (ReplaceOnly a) = a

instance (t ~ ReplaceOnly a) => Rewrapped (ReplaceOnly a) t


instance (Eq a) => Patchable (ReplaceOnly a) where
    patch (ReplaceValDelta a (Replacing da)) = ReplaceOnly $ fromMaybe a da
    diffBundle (ReplaceOnly a) (ReplaceOnly b)  =
        if (a == b)
        then ReplaceValDelta a (Replacing Nothing)
        else ReplaceValDelta a (Replacing (Just b))
      
instance PatchInstance (Replacing a) where
    (Replacing a) <^< (Replacing b) = 
        let c = case (a,b) of
                    (Nothing, x) -> x
                    (x, Nothing) -> x
                    (Just _, Just b') -> Just b'
        in Replacing c
    
instance ValDeltaBundle (ReplaceOnly a) where
    bundleVD (ReplaceOnly x,dx) = ReplaceValDelta x dx
    unbundleVD (ReplaceValDelta x dx) = (ReplaceOnly x, dx)
    valueBundle (ReplaceOnly x) = ReplaceValDelta x (Replacing Nothing)

instance DeltaRelation (ReplaceOnly String) (Replacing String) 
instance FlipDeltaRelation (Replacing String) (ReplaceOnly String)
instance ValDeltaRelation (ReplaceOnly String) (ReplaceValDelta String)
instance FlipValDeltaRelation (ReplaceValDelta String) (ReplaceOnly String)


-- $DiffNum
--
-- Difference Num's use the numeric difference as a delta. Really only works
-- for unbounded integers 'Integer'. For other types the deltas might sometimes
-- be unrepresentable, so things like @patch a (changes a b) = b@ might
-- not hold.

-- | Base type for a difference num. A 'DiffNum' is its own delta: @ILCDelta (DiffNum a) = DiffNum a@
newtype DiffNum a = DNum a
    deriving (GHC.Generic)
    deriving (Eq, Show, Num, Ord, Semigroup, Monoid) via (Sum a)
    deriving (Functor, Applicative) via Identity

data DiffNumValDelta a = DValDelta a a
    deriving (Eq, Show, Ord, GHC.Generic)

instance (Num a) => Semigroup (DiffNumValDelta a) where
    (DValDelta a da) <> (DValDelta b db) = DValDelta (a + b) (da + db)

instance (Num a) => Monoid (DiffNumValDelta a) where
    mempty = DValDelta 0 0

type instance ILCDelta (DiffNum a) = DiffNum a
type instance ValDelta (DiffNum a) = DiffNumValDelta a

instance Generic (DiffNum a)
instance Generic (DiffNumValDelta a)

instance DeltaRelation (DiffNum Integer) (DiffNum Integer)
instance FlipDeltaRelation (DiffNum Integer) (DiffNum Integer)
instance ValDeltaRelation (DiffNum Integer) (DiffNumValDelta Integer)
instance FlipValDeltaRelation (DiffNumValDelta Integer) (DiffNum Integer)


instance (Num a) => Patchable (DiffNum a) where
    patch (DValDelta a da) = DNum (a + da)
    diffBundle (DNum a) (DNum a') = DValDelta a (a' - a)

instance (Num a) => PatchInstance (DiffNum a) where
    da <^< db = da + db

instance (Num a) => ValDeltaBundle (DiffNum a) where
    bundleVD (DNum a,DNum da) = DValDelta a da
    unbundleVD (DValDelta a da) = (DNum a,DNum da)
    valueBundle (DNum a) = DValDelta a 0



-- | If a is a group, we can generate a Patchable type where the
--   delta is the same type as the actual value.
--   Patches are performed using semigroup '(<>)'.
--   Works for some numbers (Integer) but for others you
--   have the problem that some values are unrepresentable.  For instance,
--   (changes a a') on float may produce a delta that is too small to
--   represent as a float.
--
--   We need @a@ to be a group since computing @changes@ requires the inverse of @a@
newtype SelfPatchable a = SelfPatchable a
  deriving (Eq, Show)

data SelfValDelta a = SelfValDelta a a

type instance ILCDelta (SelfPatchable a) = SelfPatchable a

type instance ValDelta (SelfPatchable a) = SelfValDelta a

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

instance (Monoid a) => ValDeltaBundle (SelfPatchable a) where
  bundleVD ((SelfPatchable a), (SelfPatchable a')) = SelfValDelta a a'
  unbundleVD (SelfValDelta a a') = ((SelfPatchable a), (SelfPatchable a'))
  valueBundle (SelfPatchable a) = SelfValDelta a mempty

instance (Group a, PatchInstance a) => Patchable (SelfPatchable a) where
  patch (SelfValDelta a da) = SelfPatchable (a <> da)
  changes (SelfPatchable a) (SelfPatchable b) = SelfPatchable ((invert a) <> b)
  diffBundle (SelfPatchable a) (SelfPatchable a') = SelfValDelta a ((invert a) <> a')

instance (Ord a) => Ord (SelfPatchable a) where
  (SelfPatchable a) <= (SelfPatchable b) = a <= b

