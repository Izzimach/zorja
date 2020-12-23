{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Replaceable
    (
        ReplaceableVal(..),
        ReplaceableDelta(..),
        ReplaceableValDelta(..),
        PatchReplaceable,
        replaceable,
        replaceableChanges,
        safeBundle,
        valDeltaNoPatch,
        rCase,
        tIf,
        tBranch,


        ReplaceableMaybe(..),
        liftRM,
        toMaybeRM,
        fromMaybeRM,
        replaceableMaybe,
        unfurl,
        unfurlVal,
        unfurlAdd,
        unfurlDelete,
        CollapseReplaceableMaybe,
        collapse,

    ) where



import Prelude

import GHC.Generics

import Control.Lens.Wrapped

import Data.Maybe

import Zorja.Patchable
import Zorja.Primitives

--
-- | A wrapper around a value that can change/replace whole values;
-- used for sum types since the normal delta of sum types doesn't let you
-- switch constructors.
newtype ReplaceableVal a = ReplaceableVal { unReplaceableVal :: a }
  deriving (Generic, Eq, Show)
  
data ReplaceableDelta a = ReplaceablePatch (ILCDelta a)
                        | ReplaceableNew a
                        | ReplaceableNoPatch

data ReplaceableValDelta a where
    -- | normal value + patch that we usually expect
    ReplaceableValDelta :: ValDelta a -> ReplaceableValDelta a
    -- | replace one value with another
    ReplaceableValues :: a -> a -> ReplaceableValDelta a


instance Wrapped (ReplaceableVal a) where
    type Unwrapped (ReplaceableVal a) = a
    
instance (t ~ ReplaceableVal a) => Rewrapped (ReplaceableVal a) t

instance (Eq a, Eq (ILCDelta a)) => Eq (ReplaceableDelta a) where
    (ReplaceablePatch da) == (ReplaceablePatch da') = da == da'
    (ReplaceableNew a)    == (ReplaceableNew a')    = a == a'
    ReplaceableNoPatch    == ReplaceableNoPatch     = True
    _                     == _                      = False

instance (Show a, Show (ILCDelta a)) => Show (ReplaceableDelta a) where
    show (ReplaceablePatch da) = "ReplaceablePatch (" ++ show da ++ ")"
    show (ReplaceableNew a) = "ReplaceableNew (" ++ show a ++ ")"
    show (ReplaceableNoPatch) = "ReplaceableNoPatch"

instance Functor ReplaceableVal where
    fmap f (ReplaceableVal a) = ReplaceableVal (f a)

-- | Access 'ReplaceableValDelta' via a lens
replaceable :: forall f a. (Functor f, ValDeltaBundle a, PatchReplaceable a) =>
    (a -> f a) -> ReplaceableValDelta a -> f (ReplaceableValDelta a)
replaceable f vd = let (a, da) = unbundleVD vd
                       a' = unReplaceableVal (patch a da)
                       fa = (f a')
                       -- kind of a mess, but sometimes the constructor will switch from ReplaceValDelta
                       -- to ReplaceableValues and we have to handle this switch properly by
                       -- using replaceableChanges instead of just rebundling the result
                       rebundle = \x -> bundleVD (a, replaceableChanges (unReplaceableVal a) x)
                   in fmap rebundle fa


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



-- | Handle case statements in transformer functions.
rCase :: (ValDeltaBundle a, ValDeltaBundle b, Patchable a, Patchable b) => 
   (a -> b) -> ReplaceableValDelta a -> ValDelta b
rCase f (ReplaceableValDelta vd) = let (a,da) = unbundleVD vd
                                       a' = patch a da
                                       b  = f a
                                       b' = f a'
                                   in bundleVD (b, changes b b')
rCase f (ReplaceableValues a a') = let b = f a
                                       b' = f a'
                                       db = changes b b'
                                   in bundleVD (b,db)

rTest :: (Patchable a, ValDeltaBundle a) => (a -> Bool) -> ValDelta a -> ReplaceableValDelta Bool
rTest f vd =
    let (a,da) = unbundleVD vd
        a' = patch a da
        b = f a
        b' = f a'
    in bundleVD (ReplaceableVal b, replaceableChanges b b')

-- | Handle if in transformer functions.
--   @tIf c f g x@ represents a ValDelta version of @if (c x) then (f x) else (g x)@
tIf :: (Patchable a, Patchable b, ValDeltaBundle a, ValDeltaBundle b) =>
    (a -> Bool) -> (a -> b) -> (a -> b) -> ValDelta a -> ValDelta b
tIf c f g vd =
    let test = rTest c vd
    in tBranch (liftVD f) (liftVD g) test vd

-- | Pick one of two functions from @ValDelta a -> Valdelta b@ based on a 'ReplaceableValDelta Bool' value.
tBranch :: (Patchable b, ValDeltaBundle b) =>
    (ValDelta a -> ValDelta b) -> 
    (ValDelta a -> ValDelta b) -> 
    ReplaceableValDelta Bool -> 
    (ValDelta a -> ValDelta b)
tBranch f g t vd =
    case t of
        (ReplaceableValDelta (BoolVD x)) -> pickFunc x $ vd
        (ReplaceableValues x x')         -> let (b ,db)  = unbundleVD $ pickFunc x  vd
                                                (b',db') = unbundleVD $ pickFunc x' vd
                                            in bundleVD (b, changes b (patch b' db'))
    where
        pickFunc b = if b then f else g
        

-- | Normally you don't use raw 'Maybe' as a value/delta type since as a sum type it
--   can produce mismatch errors. Instead you will typically use @ReplaceableVal (Maybe a)@
--   which is represented by the 'ReplaceableMaybe' newtype.
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
    safeBundle (v,BoolD) = BoolVD v

    valDeltaNoPatch :: Bool -> BoolVD
    valDeltaNoPatch v = BoolVD v


newtype ReplaceableMaybe a = ReplaceableMaybe (ReplaceableValDelta (Maybe a))
    deriving (Generic)

instance Wrapped (ReplaceableMaybe a) where
    type Unwrapped (ReplaceableMaybe a) = ReplaceableValDelta (Maybe a)
    
instance (t ~ ReplaceableMaybe a) => Rewrapped (ReplaceableMaybe a) t

instance (Show a, Show (ValDelta a), Show (ReplaceableValDelta a)) => Show (ReplaceableMaybe a) where
    show (ReplaceableMaybe x) = "ReplaceableMaybe (" ++ show x ++ ")"

class CollapseReplaceableMaybe a where
    collapse :: ReplaceableMaybe a -> ValDelta a
    unfurl :: ValDelta a -> ReplaceableMaybe a

instance (Monoid a, Eq a) => CollapseReplaceableMaybe (ReplaceOnly a) where
    collapse (ReplaceableMaybe vd) = case vd of
        ReplaceableValDelta Nothing -> bundleVD (mempty, noPatch)
        ReplaceableValDelta (Just vda) -> vda
        ReplaceableValues a a'         -> let x = fromMaybe mempty a
                                              x' = fromMaybe mempty a'
                                          in bundleVD (x, changes x x')
    unfurl v = ReplaceableMaybe $
                 let (ReplaceOnly r,Replacing dr) = unbundleVD v
                 in case dr of
                   Nothing -> ReplaceableValDelta $ Just v
                   Just da -> case (nullEmpty r, nullEmpty da) of
                                (Nothing, Nothing) -> ReplaceableValDelta Nothing
                                (Just _, Just _)   -> ReplaceableValDelta (Just v)
                                -- fallback is if one or the other is Nothing, in which
                                -- case we need to use ReplaceableValues
                                (x, x')            -> ReplaceableValues (fmap ReplaceOnly x) (fmap ReplaceOnly x')
        where
            nullEmpty x = if (x == mempty) then Nothing else Just x


liftRM :: (ValDeltaBundle a, Patchable a, ValDeltaBundle b, Patchable b) =>
    (ValDelta a -> ValDelta b) -> ReplaceableMaybe a -> ReplaceableMaybe b
liftRM fvd =
    \(ReplaceableMaybe arm) -> case arm of
        ReplaceableValDelta va -> ReplaceableMaybe $ ReplaceableValDelta (fmap fvd va)
        ReplaceableValues a a' -> let f = lowerVD fvd 
                                  in ReplaceableMaybe $ ReplaceableValues (fmap f a) (fmap f a')

toMaybeRM :: (Eq a, Eq (ValDelta a)) => ReplaceableMaybe a -> Maybe (ReplaceableMaybe a)
toMaybeRM a@(ReplaceableMaybe x)
    | x == ReplaceableValues Nothing Nothing     = Nothing
    | otherwise                                  = Just a

fromMaybeRM :: Maybe (ReplaceableMaybe a) -> ReplaceableMaybe a
fromMaybeRM Nothing = ReplaceableMaybe (ReplaceableValues Nothing Nothing)
fromMaybeRM (Just v) = v


-- | Access 'ReplaceableMaybe' via a lens. This picks out the @Maybe a@ inside, so you can
--   add or remove values.
--   If you want to work with @a@ instead, add a '_Just' to the end of it.
replaceableMaybe :: forall f a. (Functor f, Patchable a, ValDeltaBundle a) =>
    (Maybe a -> f (Maybe a)) -> ReplaceableMaybe a -> f (ReplaceableMaybe a)
replaceableMaybe = _Wrapped . replaceable

-- | Convert a single value into a 'ReplaceableMaybe' that represents a value with an empty ('noPatch') delta
unfurlVal :: (ValDeltaBundle a, Patchable a) => a -> ReplaceableMaybe a
unfurlVal a = ReplaceableMaybe $ ReplaceableValDelta $ Just (bundleVD (a,noPatch))

-- | Convert a single value into a 'ReplaceableMaybe' that represents adding a value
unfurlAdd :: a -> ReplaceableMaybe a
unfurlAdd a = ReplaceableMaybe $ ReplaceableValues Nothing (Just a)
             
-- | Convert a single value into a 'ReplaceableMaybe' that represents deleting a value
unfurlDelete :: a -> ReplaceableMaybe a
unfurlDelete a = ReplaceableMaybe $ ReplaceableValues (Just a) Nothing
             

instance (Eq a, Num a) => CollapseReplaceableMaybe (DiffNum a) where
    collapse (ReplaceableMaybe v) = case v of
        ReplaceableValDelta Nothing -> bundleVD (0, noPatch)
        ReplaceableValDelta (Just vda) -> vda
        ReplaceableValues a a'         -> let x = fromMaybe 0 a
                                              x' = fromMaybe 0 a'
                                          in bundleVD (x, changes x x')

    unfurl (DValDelta a da) = ReplaceableMaybe $
                      let x = nullZero (DNum a)
                          dx = nullZero (DNum da)
                      in case (x,dx) of
                        (Nothing, Nothing) -> ReplaceableValDelta Nothing
                        (Just v, Just dv) -> ReplaceableValDelta $ Just (bundleVD (v,dv))
                        (_,_)             -> ReplaceableValues x dx
        where
            nullZero x = if (x == 0) then Nothing else Just x

