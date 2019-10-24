{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Primitives 
    (
        --IdentityD(..),
        ReplaceOnly(..),
        Replacing(..),
        DiffNum(..)
    )
    where

import Data.Functor.Identity
import Data.Semigroup
import Data.Maybe

import Zorja.Patchable
import Zorja.FunctorDExpr
import Zorja.ZHOAS

-- | Deltas for Identity

newtype FIdentity f a = FIdentity (f a)
    deriving (Eq, Show) via (f a)
    deriving (Semigroup, Monoid) via (f a)

type instance PatchDelta (FIdentity f a) = FIdentity (FunctorDelta f) a
type instance FunctorDelta (FIdentity f) = FIdentity (FunctorDelta f)

instance (Patchable (f a), PatchInstance (FunctorDelta f a), FDECompatible f, FDEConvertible f a) => Patchable (FIdentity f a) where
    patch (FIdentity a) (FIdentity da) = FIdentity (patch a (fromFD da))
    changes (FIdentity a) (FIdentity a') = FIdentity $ toFD (changes a a')

instance (PatchInstance (f a)) => PatchInstance (FIdentity f a) where
    mergepatches (FIdentity da) (FIdentity da') = FIdentity (mergepatches da da')
    nopatch = FIdentity nopatch

instance (FDECompatible f) => FDECompatible (FIdentity f) where
    type FDEConstraint (FIdentity f) a = (Patchable (f a), PatchInstance (FunctorDelta f a), FDECompatible f, FDEConvertible f a)
    toFDE z = let (v,dv) = zdEval z
              in
                  FDE v dv
    fromFDE (FDE a da) = ZDV a da
    --fmapFD f (FIdentityD x) = FIdentityD $ fmap f x

instance (Functor f) => Functor (FIdentity f) where
    fmap f (FIdentity a) = FIdentity (fmap f a)

instance (FDEFunctor f, FDECompatible f) => FDEFunctor (FIdentity f) where
    --fmapFDE :: (a -> b) -> FunctorDExpr FIdentity a -> FunctorDExpr FIdentity b
    fmapFDE f (FDE (FIdentity x) (FIdentity dx)) =
        let (FDE x' dx') = fmapFDE f (FDE x dx)
        in
            FDE (FIdentity x') (FIdentity dx')    

--
-- ReplaceOnly and Reaplacing datatypes
--


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

type instance PatchDelta (ReplaceOnly a) = Replacing a
--type instance UnPatchDelta (Replacing a) = ReplaceOnly a

type instance FunctorDelta ReplaceOnly = Replacing
--type instance UnFunctorDelta Replacing = ReplaceOnly

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
                    (Just _, Just b') -> Just b'
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
    --toFD (Replacing a) = Replacing a
    --fromFD (Replacing a) = Replacing a

instance FDEFunctor ReplaceOnly where
    --fmapFD f x = fmap f x
    fmapFDE f (FDE x dx) = FDE (fmap f x) (fmap f dx)


--
-- | Difference Num's use the numeric difference as a delta. Really only works
--   for unbounded integers 'Integer'. For other types the deltas might sometimes
--   be unrepresentable, so things like @patch a (changes a b) = b@ might
--   not hold.
newtype DiffNum a = DNum (Sum a)
    deriving (Eq, Show, Num, Ord, Semigroup, Monoid) via (Sum a)
    deriving (Functor, Applicative) via Identity

type instance PatchDelta (DiffNum a) = DiffNum a
type instance FunctorDelta DiffNum = DiffNum

instance (Num a, Eq a) => Patchable (DiffNum a) where
    patch a da = a + da
    changes a a' = a' - a

instance (Num a) => PatchInstance (DiffNum a) where
    mergepatches da db = da + db
    nopatch = DNum mempty
    
