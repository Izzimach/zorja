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
        -- * A number where the delta is of the same numeric type
        --
        -- $diffNum
        DiffNum(..),

        ReplaceableVal(..),
        ReplaceableDelta(..),
        ReplaceableValDelta(..),
        PatchReplaceable,
        replaceableChanges,
        safeBundle,
        valDeltaNoPatch,

        ifILC
    )
    where

import GHC.Generics

import Control.Lens.Wrapped

import Data.Functor.Identity
import Data.Semigroup
import Data.Maybe
import Data.Hashable


import Zorja.Patchable
import Zorja.Combine


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

type instance ILCDelta (ReplaceOnly a) = Replacing a
type instance ValDelta (ReplaceOnly a) = (ReplaceOnly a, Replacing a)

instance Wrapped (ReplaceOnly a) where
    type Unwrapped (ReplaceOnly a) = a

instance (Eq a) => Patchable (ReplaceOnly a) where
    patch (ReplaceOnly a) (Replacing da) = ReplaceOnly $ fromMaybe a da
    changes (ReplaceOnly a) (ReplaceOnly b) =
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
    noPatch = Replacing Nothing
    
instance ValDeltaBundle (ReplaceOnly a) where
    bundleVD = id
    unbundleVD = id

--
-- wrapper around a value that can change/replace whole values;
-- used for sum types mostly but useful for recursive types where
-- simple
--

newtype ReplaceableVal a = ReplaceableVal a
  deriving (Generic, Eq, Show)

instance Wrapped (ReplaceableVal a) where
    type Unwrapped (ReplaceableVal a) = a
    

data ReplaceableDelta a = ReplaceablePatch (ILCDelta a)
                        | ReplaceableNew a
                        | ReplaceableNoPatch

instance (Eq a, Eq (ILCDelta a)) => Eq (ReplaceableDelta a) where
    (ReplaceablePatch da) == (ReplaceablePatch da') = da == da'
    (ReplaceableNew a)    == (ReplaceableNew a')    = a == a'
    ReplaceableNoPatch    == ReplaceableNoPatch     = True
    _                     == _                      = False

instance (Show a, Show (ILCDelta a)) => Show (ReplaceableDelta a) where
    show (ReplaceablePatch da) = "ReplaceablePatch (" ++ show da ++ ")"
    show (ReplaceableNew a) = "ReplaceableNew (" ++ show a ++ ")"
    show (ReplaceableNoPatch) = "ReplaceableNoPatch"

data ReplaceableValDelta a where
    ReplaceableValDelta :: ValDelta a -> ReplaceableValDelta a
      -- ^ normal value + patch
    ReplaceableValues :: a -> a -> ReplaceableValDelta a           -- ^ replace one value with another

instance Functor (ReplaceableValDelta) where
    fmap f (ReplaceableValDelta v) = undefined

    fmap f (ReplaceableValues a a') = ReplaceableValues (f a) (f a')

instance (Eq a, Eq (ValDelta a)) => Eq (ReplaceableValDelta a) where
    (ReplaceableValDelta da) == (ReplaceableValDelta da')  = (da == da')
    (ReplaceableValues a b)  == (ReplaceableValues a' b')  = (a == a') && (b == b')
    _                        == _                          = False

instance (Show a, Show (ValDelta a)) => Show (ReplaceableValDelta a) where
    show (ReplaceableValDelta vd) = "ReplaceableValDelta (" ++ show vd ++ ")"
    show (ReplaceableValues a a') = "ReplaceableValues (" ++ show a ++ ") (" ++ show a' ++ ")"

type instance ILCDelta (ReplaceableVal a) = ReplaceableDelta a
type instance ValDelta (ReplaceableVal a) = ReplaceableValDelta a

class (Patchable a) => PatchReplaceable a where
  replaceableChanges :: a -> a -> ReplaceableDelta a
  safeBundle :: (a, ILCDelta a) -> ValDelta a
  valDeltaNoPatch :: a -> ValDelta a

instance (PatchReplaceable a, PatchInstance (ILCDelta a)) => Patchable (ReplaceableVal a) where
  patch (ReplaceableVal x) (ReplaceablePatch dx) = ReplaceableVal (patch x dx)
  patch (ReplaceableVal _) (ReplaceableNew   x') = ReplaceableVal x'
  patch x                  ReplaceableNoPatch    = x

  changes (ReplaceableVal a) (ReplaceableVal a') = replaceableChanges a a'

instance (PatchReplaceable a, PatchInstance (ILCDelta a)) => PatchInstance (ReplaceableDelta a) where
  x                     <^< ReplaceableNoPatch     = x
  (ReplaceableNew    x) <^< (ReplaceablePatch dx)  = ReplaceableNew (patch x dx)
  (ReplaceablePatch dx) <^< (ReplaceablePatch dx') = ReplaceablePatch (dx <^< dx')
  ReplaceableNoPatch    <^< (ReplaceablePatch dx)  = ReplaceablePatch dx
  _                     <^< (ReplaceableNew   x')  = ReplaceableNew x'

  noPatch = ReplaceableNoPatch

instance (PatchReplaceable a, ValDeltaBundle a) => ValDeltaBundle (ReplaceableVal a) where
    bundleVD (ReplaceableVal x, y) =
        case y of
            (ReplaceablePatch dx) -> ReplaceableValDelta (safeBundle (x, dx))
            (ReplaceableNew x') -> ReplaceableValues x x'
            ReplaceableNoPatch -> ReplaceableValDelta (valDeltaNoPatch x)

    unbundleVD (ReplaceableValDelta v) = let (x,dx) = unbundleVD v
                                         in (ReplaceableVal x, ReplaceablePatch dx)
    unbundleVD (ReplaceableValues x x') = (ReplaceableVal x, ReplaceableNew x')

instance (Patchable a, ValDeltaBundle a) => PatchReplaceable (Maybe a) where
  replaceableChanges Nothing (Just x) = ReplaceableNew (Just x)
  replaceableChanges (Just _) Nothing = ReplaceableNew Nothing
  replaceableChanges Nothing Nothing  = ReplaceableNoPatch
  replaceableChanges (Just x) (Just x') = ReplaceablePatch $ Just (changes x x')

  safeBundle (Nothing, _) = Nothing
  safeBundle (Just x, Just dx) = Just (bundleVD (x,dx))
  safeBundle (Just x, Nothing) = Just (bundleVD (x, noPatch))

  valDeltaNoPatch Nothing = Nothing
  valDeltaNoPatch (Just x) = Just (bundleVD (x, noPatch))

instance PatchReplaceable Bool where
    replaceableChanges :: Bool -> Bool -> ReplaceableDelta Bool
    replaceableChanges True True   = ReplaceableNoPatch
    replaceableChanges False False = ReplaceableNoPatch
    replaceableChanges _ b         = ReplaceableNew b
    
    safeBundle :: (Bool, BoolD) -> BoolVD
    safeBundle (v,d) = BoolVD v d

    valDeltaNoPatch :: Bool -> BoolVD
    valDeltaNoPatch v = BoolVD v BoolD




--
-- Safe patchable with Generics
--
{-
class PatchReplaceableG x where
  replaceableChangesG :: x p -> x p -> (ReplaceableDelta rx)

instance (PatchReplaceable x) => PatchReplaceableG (K1 a x)where
  replaceableChangesG (K1 x) (K1 x') = case (replaceableChanges x x') of
                                           ReplaceablePatch dx -> ReplaceablePatch $ to (K1 dx)
                                           ReplaceableNew   x2 -> ReplaceableNew $ to (K1 x2)
                                           ReplaceableNoPatch  -> ReplaceableNoPatch

--instance (PatchReplaceableG x, PatchReplaceableG y) => PatchReplaceableG (x :*: y) where
--    replaceableChangesG (x :*: y) (x' :*: y') = _f (replaceableChangesG x x') (replaceableChangesG y y')

instance (PatchReplaceableG x, PatchReplaceableG y) => PatchReplaceableG (x :+: y) where
    replaceableChangesG (L1 x) (L1 x') = case (replaceableChangesG x x') of
                                           ReplaceablePatch dx -> ReplaceablePatch $ L1 (_l dx)
                                           ReplaceableNew   x2 -> ReplaceableNew (L1 x2)
                                           ReplaceableNoPatch  -> ReplaceableNoPatch


class SafeBundleG x dx v where
  safeBundleG :: (x :*: dx) p -> v p
  valDeltaNoPatchG :: x p -> v p

instance (SafePatchable x, rx ~ ReplaceableDelta x) => SafePatchableG (K1 a x) (K1 x rx) where
  safeChangesG (K1 x) (K1 x') = K1 $ safeChanges x x'

instance (SafePatchableG (x) x', SafePatchableG (y) y') => SafePatchableG ((x :*: y)) (x' :*: y') where
    safeChangesG (x :*: y) (x' :*: y') = (safeChangesG x x') :*: (safeChangesG y y')

instance (SafePatchableG (x p) (rx p), SafePatchableG (y p) (rx p), rx ~ ReplaceableDelta (x :+: y)) => SafePatchableG (x :+: y) rx where
    safeChangesG (L1 x) (L1 x') = L1 $ safeChangesG x x'
    safeChangesG (R1 y) (R1 y') = R1 $ safeChangesG y y'
    safeChangesG (L1 x) (R1 y)  = L1 $ ReplaceableNew (R1 y)

instance (SafePatchable x, dx ~ ILCDelta x, ValDelta x ~ v) => SafeBundleG (K1 a x) (K1 a dx) (K1 a v) where
  safeBundleG (K1 x :*: K1 dx) = K1 $ safeBundle (x, dx)
  valDeltaNoPatchG (K1 x) = K1 $ valDeltaNoPatch x
-}
-- $DiffNum
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

wrapIf :: (Patchable a, ValDeltaBundle a) => (Bool -> a) -> ((ReplaceableValDelta Bool) -> ValDelta a)
wrapIf f rv = 
    case rv of
        ReplaceableValues b b' -> let a = f b
                                      a' = f b'
                                      da = changes a a'
                                  in
                                      bundleVD (a,da)
        ReplaceableValDelta (BoolVD b BoolD) -> bundleVD (f b, noPatch)

wrapTest :: (Patchable a, ValDeltaBundle a) => (a -> Bool) -> ValDelta a -> (ReplaceableValDelta Bool)
wrapTest f va = let (a,da) = unbundleVD va
                    b = f a
                    b' = f (patch a da)
                in
                    bundleVD (ReplaceableVal b, replaceableChanges b b')

ifILC :: (Patchable a, Patchable b, ValDeltaBundle a, ValDeltaBundle b) =>
    (a -> Bool) -> (Bool -> b) -> (ValDelta a) -> (ValDelta b)
ifILC b f = (wrapIf f) . (wrapTest b)  