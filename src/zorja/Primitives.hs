{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Zorja.Primitives 
    (
        ReplaceOnly(..),
        Replacing(..)
    )
    where

import Data.Functor.Identity
import Data.Semigroup
import Data.Text
import Data.Maybe
import Data.Monoid hiding (Last)

import Control.Applicative

import Zorja.Patchable
import Zorja.FunctorDExpr
import Zorja.ZHOAS

-- | ReplaceOnly is a 'Patchable' type that just replaces the
--  previous value. Efficient for primitive types, but
--  larger data structures should use something more clever
newtype ReplaceOnly a = ReplaceOnly a
    deriving (Eq, Show)
    deriving (Functor, Applicative) via Identity
    deriving (Semigroup, Monoid, Num, Ord) via (Identity a)

-- | 'Replacing a' is the 'PatchDelta' of 'ReplaceOnly'. It 
--  behaves as 'Maybe a' when used as a 'Monoid'. However, it
--  behaves as 'Option (Last a)' when used as a 'PatchInstance'
newtype Replacing a = Replacing (Maybe a)
    deriving (Eq, Show)
    deriving (Functor, Applicative) via Maybe
    deriving (Semigroup, Monoid) via (Maybe a)

type instance PatchDelta (ReplaceOnly a) = Replacing a
type instance FunctorDelta ReplaceOnly = Replacing


instance (Eq a) => Patchable (ReplaceOnly a) where
    patch (ReplaceOnly a) (Replacing da) = ReplaceOnly $ fromMaybe a da
    changes (ReplaceOnly a) (ReplaceOnly b) =
        if (a == b)
        then Replacing Nothing
        else Replacing $ Just $ b
      
instance PatchInstance (Replacing a) where
    mergepatches (Replacing a) (Replacing b) = 
        let c = case (a,b) of
                    (Nothing, x) -> x
                    (x, Nothing) -> x
                    (Just a', Just b') -> Just b'
        in Replacing c
    nopatch = Replacing Nothing

    
    
instance (Semigroup a) => Semigroup (FunctorDExpr ReplaceOnly a) where
    (FDE (ReplaceOnly a) (Replacing da)) <> (FDE (ReplaceOnly b) (Replacing db)) =
            let c = case (da,db) of
                    -- short-circuit if both a and b don't change
                    (Nothing, Nothing) -> Nothing
                    (a',b') -> Just $ (fromMaybe a a') <> (fromMaybe b b')
            in
                FDE (ReplaceOnly $ a <> b) (Replacing c)

instance (Monoid a) => Monoid (FunctorDExpr ReplaceOnly a) where
    mempty = FDE mempty mempty

--
-- FunctorDExpr implementations for ReplaceOnly
--
    
instance FDECompatible ReplaceOnly where
    type FDEConstraint ReplaceOnly a = (Eq a)
    toFDE z = let (v,dv) = zdEval z
              in FDE v dv
    fromFDE (FDE a da) = ZDV a da
    toFD (Replacing a) = Replacing a
    fromFD (Replacing a) = Replacing a

instance FDEFunctor ReplaceOnly where
    fmapFD f x = fmap f x
    fmapFDE f (FDE x dx) = FDE (fmap f x) (fmap f dx)
