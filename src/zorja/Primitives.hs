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
    )
    where

import Prelude

import GHC.Generics

import Control.Lens.Wrapped

import Data.Functor.Identity
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
--  previous value. Efficient for primitive types, but
--  larger data structures should use something more clever
newtype ReplaceOnly a = ReplaceOnly a
    deriving (Eq, Show, Generic)
    deriving (Functor, Applicative) via Identity
    deriving (Semigroup, Monoid, Num, Ord) via a

-- | 'Replacing a' is the 'PatchDelta' of 'ReplaceOnly'. It 
--  behaves as 'Maybe a' when used as a 'Monoid'. However, it
--  behaves as 'Option (Last a)' when used as a 'PatchInstance'
newtype Replacing a = Replacing (Maybe a)
    deriving (Eq, Show, Generic)
    deriving (Functor, Applicative) via Maybe
    deriving (Semigroup, Monoid) via (Maybe a)

data ReplaceValDelta a = ReplaceValDelta a (Replacing a)
    deriving (Eq, Show, Generic)

type instance ILCDelta (ReplaceOnly a) = Replacing a
type instance ValDelta (ReplaceOnly a) = ReplaceValDelta a

instance Wrapped (ReplaceOnly a) where
    type Unwrapped (ReplaceOnly a) = a

instance (t ~ ReplaceOnly a) => Rewrapped (ReplaceOnly a) t


instance (Eq a) => Patchable (ReplaceOnly a) where
    patch (ReplaceValDelta a (Replacing da)) = ReplaceOnly $ fromMaybe a da
    changes (ReplaceOnly a) (ReplaceOnly b)  =
        if (a == b)
        then Replacing Nothing
        else Replacing (Just b)
      
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


-- $DiffNum
--
-- Difference Num's use the numeric difference as a delta. Really only works
-- for unbounded integers 'Integer'. For other types the deltas might sometimes
-- be unrepresentable, so things like @patch a (changes a b) = b@ might
-- not hold.

-- | Base type for a difference num. A 'DiffNum' is its own delta: @ILCDelta (DiffNum a) = DiffNum a@
newtype DiffNum a = DNum a
    deriving (Eq, Show, Num, Ord, Semigroup, Monoid) via (Sum a)
    deriving (Functor, Applicative) via Identity

data DiffNumValDelta a = DValDelta a a
    deriving (Eq, Show, Ord)

instance (Num a) => Semigroup (DiffNumValDelta a) where
    (DValDelta a da) <> (DValDelta b db) = DValDelta (a + b) (da + db)

instance (Num a) => Monoid (DiffNumValDelta a) where
    mempty = DValDelta 0 0

type instance ILCDelta (DiffNum a) = DiffNum a
type instance ValDelta (DiffNum a) = DiffNumValDelta a

instance (Num a) => Patchable (DiffNum a) where
    patch (DValDelta a da) = DNum (a + da)
    changes a a' = a' - a

instance (Num a) => PatchInstance (DiffNum a) where
    da <^< db = da + db

instance (Num a) => ValDeltaBundle (DiffNum a) where
    bundleVD (DNum a,DNum da) = DValDelta a da
    unbundleVD (DValDelta a da) = (DNum a,DNum da)
    valueBundle (DNum a) = DValDelta a 0

