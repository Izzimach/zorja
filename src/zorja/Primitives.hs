{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Primitives 
    (
        -- * Identity for deferred functors
        FIdentity(..),
        -- * A type where the delta simply replaces old values
        --
        -- $replaceOnly
        ReplaceOnly(..),
        Replacing(..),
        ReplaceOnlyK,
        -- * A number where the delta is of the same numeric type
        --
        -- $diffNum
        DiffNum(..)
    )
    where

import Data.Functor.Identity
import Data.Semigroup
import Data.Maybe

import Fcf.Core

import Zorja.Patchable
import Zorja.FunctorDExpr

-- | Deltas for Identity

data IdentityK :: DeferredFunctor k

newtype FIdentity a = FIdentity a

type instance Eval (ReifyFunctor  IdentityK a) = FIdentity a
type instance Eval (ReifyFunctorD IdentityK a) = FIdentity a

instance Functor (FIdentity) where
    fmap f (FIdentity a) = FIdentity (f a)

instance ReifyFmap IdentityK where
    rfmap _ f (FIdentity a) = FIdentity (f a)
    rfmapD _ f (FIdentity a) = FIdentity (f a)
    
type instance ILCDelta (FIdentity a) = FIdentity a

instance (PatchInstance a) => PatchInstance (FIdentity a) where
    (FIdentity da) <^< (FIdentity da') = FIdentity (da <^< da')
    noPatch = FIdentity noPatch




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
    deriving (Eq, Show)
    deriving (Functor, Applicative) via Identity
    deriving (Semigroup, Monoid, Num, Ord) via a

-- | 'Replacing a' is the 'PatchDelta' of 'ReplaceOnly'. It 
--  behaves as 'Maybe a' when used as a 'Monoid'. However, it
--  behaves as 'Option (Last a)' when used as a 'PatchInstance'
newtype Replacing a = Replacing (Maybe a)
    deriving (Eq, Show)
    deriving (Functor, Applicative) via Maybe
    deriving (Semigroup, Monoid) via (Maybe a)

type instance ILCDelta (ReplaceOnly a) = Replacing a

instance ReifyFmap ReplaceOnlyK where
    rfmap _ f (ReplaceOnly a) = ReplaceOnly (f a)
    rfmapD _ f (Replacing da) = Replacing   (fmap f da)


instance (Eq a) => Patchable (ReplaceOnly a) where
    patch (ReplaceOnly a) (Replacing da) = ReplaceOnly $ fromMaybe a da
    changes (ReplaceOnly a) (ReplaceOnly b) =
        if (a == b)
        then Replacing Nothing
        else Replacing $ Just $ b
      
instance PatchInstance (Replacing a) where
    (Replacing a) <^< (Replacing b) = 
        let c = case (a,b) of
                    (Nothing, x) -> x
                    (x, Nothing) -> x
                    (Just _, Just b') -> Just b'
        in Replacing c
    noPatch = Replacing Nothing

-- | a kind to use 'ReplaceOnly' with deferred functors found in 'Zorja.FunctorDExpr'
data ReplaceOnlyK :: DeferredFunctor k

type instance Eval (ReifyFunctor ReplaceOnlyK a) = ReplaceOnly a
type instance Eval (ReifyFunctorD ReplaceOnlyK a) = Replacing a

    





-- $diffNum
--
-- Difference Num's use the numeric difference as a delta. Really only works
-- for unbounded integers 'Integer'. For other types the deltas might sometimes
-- be unrepresentable, so things like @patch a (changes a b) = b@ might
-- not hold.

-- | Base type for a difference num. A 'DiffNum' is its own delta: @ILCDelta (DiffNum a) = DiffNum a@
newtype DiffNum a = DNum (Sum a)
    deriving (Eq, Show, Num, Ord, Semigroup, Monoid) via (Sum a)
    deriving (Functor, Applicative) via Identity

type instance ILCDelta (DiffNum a) = DiffNum a

instance (Num a) => Patchable (DiffNum a) where
    patch a da = a + da
    changes a a' = a' - a

instance (Num a) => PatchInstance (DiffNum a) where
    da <^< db = da + db
    noPatch = DNum mempty
