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

import Control.Applicative

import Fcf

import Data.Proxy
import Data.Functor.Foldable

import Zorja.Patchable
import Zorja.ZHOAS
import Zorja.FunctorDExpr

-- | A 'DeferredFunctor' kind to indicate 'ListX' and 'ListXD'
data ListXK (d :: DeferredFunctor k) :: DeferredFunctor k

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
newtype ListXD a = ListXD [a]
    deriving (Eq, Show)
    deriving (Applicative, Functor, Foldable) via []

type instance Eval (ReifyFunctor  (ListXK d) a) = ListX  (Eval (ReifyFunctor d a))
type instance Eval (ReifyFunctorD (ListXK d) a) = ListXD (Eval (ReifyFunctorD d a))

type instance ILCDelta (ListX a) = ListXD (ILCDelta a)


{-newtype ListX f a = ListX [Eval (ReifyFunctor f a)]
    deriving (Eq, Show)
    deriving (Semigroup, Monoid) via [f a]-}

instance (ReifyFmap d) => ReifyFmap (ListXK d) where
    rfmap _p f (ListX  a)  = ListX  $ fmap (rfmap (Proxy @d) f) a
    rfdmap _ f (ListXD da) = ListXD $ fmap (rfdmap (Proxy @d) f) da
    


instance (PatchInstance a) => PatchInstance (ListXD a) where
    (ListXD a) <^< (ListXD b) = ListXD $ zipWith (<^<) a b
    -- this is an infinite empty list
    noPatch = ListXD $ repeat noPatch

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

