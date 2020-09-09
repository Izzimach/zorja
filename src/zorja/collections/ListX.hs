{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Collections.ListX where

import Fcf

import Data.Proxy
import Data.Functor.Foldable

import Zorja.Patchable
import Zorja.FunctorDExpr

-- | 'ListX' is basically a list that supports 'RFType'
--  and thus deferred functors.
--  The 'ListX' type is meant for experimental and testing
--  purposes, since it has several drawbacks:
--  - The delta cannot represent adding or removing elements from the list
--  - To rearrange or swap elements you basically have to destroy the elements
--    and rebuild them in their new positions.
newtype ListX a  = ListX [a]
    deriving (Eq, Show)
    deriving (Applicative, Functor, Foldable) via []
    deriving (Semigroup,Monoid) via [a]

-- | 'ListXD (ILCDelta a)' is @ILCDelta (ListX a)@
newtype ListXD a = ListXD [a]
    deriving (Eq, Show)
    deriving (Applicative, Functor, Foldable) via []
    deriving (Semigroup,Monoid) via [a]

type instance ILCDelta (ListX a) = ListXD (ILCDelta a)

type instance ValDelta (ListX a) = ListX (ValDelta a)

instance (ValDeltaBundle a) => ValDeltaBundle (ListX a) where
  bundleVD :: (ListX a, ListXD (ILCDelta a)) -> ListX (ValDelta a)
  bundleVD (ListX a, ListXD da) = ListX $ zipWith (curry bundleVD) a da
  unbundleVD :: ListX (ValDelta a) -> (ListX a, ListXD (ILCDelta a))
  unbundleVD (ListX x) = let (a,da) = unzip $ fmap unbundleVD x
                         in (ListX a, ListXD da)



{-newtype ListX f a = ListX [Eval (ReifyFunctor f a)]
    deriving (Eq, Show)
    deriving (Semigroup, Monoid) via [f a]-}

instance (PatchInstance a) => PatchInstance (ListXD a) where
    (ListXD a) <^< (ListXD b) = ListXD $ zipWith (<^<) a b
    -- missing items are 'noaPatch' this is an empty list
    noPatch = ListXD []

instance (Patchable a,PatchInstance (ILCDelta a)) => Patchable (ListX a) where
    patch (ListX a) (ListXD da) = ListX $ zipWith patch a da
    changes (ListX a) (ListX a') = ListXD $ zipWith changes a a'


-- | Non-recursive functor representation of 'ListX' for 'recursion-schemes'
data ListXF a x = 
      ConsX a x 
    | NilX
    deriving (Eq, Show)
    
instance Functor (ListXF a) where
    fmap f (ConsX a b) = ConsX a (f b)
    fmap _f NilX        = NilX

type instance Base (ListX a) = ListXF a
    
instance Recursive (ListX a) where
    project (ListX [])     = NilX
    project (ListX (x:xs)) = ConsX x (ListX xs)

instance Corecursive (ListX a) where
    embed (ConsX x (ListX xs)) = ListX (x:xs)
    embed NilX                 = ListX []


-- | Non-recursive functor representation of 'ListXD' for 'recursion-schemes'
data ListXFD a x = 
      ConsXD a x
    | NilXD
    deriving (Eq, Show)
    
instance Functor (ListXFD a) where
    fmap f (ConsXD a b) = ConsXD a (f b)
    fmap _f NilXD       = NilXD

type instance Base (ListXD a) = ListXFD a
    
instance Recursive (ListXD a) where
    project (ListXD [])     = NilXD
    project (ListXD (x:xs)) = ConsXD x (ListXD xs)

instance Corecursive (ListXD a) where
    embed (ConsXD x (ListXD xs)) = ListXD (x:xs)
    embed NilXD                  = ListXD []

