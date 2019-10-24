{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.FunctorDExpr where

import Data.Distributive
import Data.Kind (Type, Constraint)

import Zorja.Patchable
import Zorja.ZHOAS
    

-- |'FunctorDExpr' is a 'ZDExpr' where both 'a' and 'da' can be expressed as
-- functors. You can switch between the two using 'toFDE' and 'fromFDE'

data FunctorDExpr f a = FDE (f a) (FunctorDelta f a)

instance (Functor f, Functor (FunctorDelta f)) => Functor (FunctorDExpr f) where
    fmap f (FDE fa dfa) = FDE (fmap f fa) (fmap f dfa)

instance (Foldable f, Foldable (FunctorDelta f)) => Foldable (FunctorDExpr f) where
    foldMap f (FDE fa dfa) = (foldMap f fa) <> (foldMap f dfa)

instance (Distributive f, Distributive (FunctorDelta f)) => Distributive (FunctorDExpr f) where
    distribute xs = FDE (collect getA xs) (collect getDA xs)
        where
            getA (FDE a _) = a
            getDA (FDE _ b) = b

instance (Traversable f, Traversable (FunctorDelta f)) => Traversable (FunctorDExpr f) where
    traverse f (FDE fa dfa) = FDE <$> (traverse f fa) <*> (traverse f dfa)

-- | 'FDEConvertible' indicates that for a functor type 'f' the types
--  'PatchDelta' and 'FunctorDelta' are equivalent. Thus @ZDExpr (f a)@ can
--  be converted to @FunctorDExpr f a@
type FDEConvertible f a = (FDEConstraint f a, PatchDelta (f a) ~ FunctorDelta f a)

-- |'FDEConvertible' is for 'Functor's (and their associated 'FunctorDelta')
-- that can be converted between 'ZDExpr' 'FunctorDExpr'

class FDECompatible (f :: Type -> Type) where
    type FDEConstraint f a :: Constraint

    toFDE   :: (FDEConvertible f a) => ZDExpr (f a) -> FunctorDExpr f a
    fromFDE :: (FDEConvertible f a) => FunctorDExpr f a -> ZDExpr (f a)
    toFD   :: (FDEConvertible f a) => PatchDelta (f a) -> FunctorDelta f a
    fromFD :: (FDEConvertible f a) => FunctorDelta f a -> PatchDelta (f a)


-- | A 'FDFunctor' allows you to take a function normally used to 'fmap'
--  on a functor 'fd' and instead apply it to a
-- 'FunctorDelta fd' or 'FunctorDExpr fd'
class (FDECompatible f) => FDEFunctor f where
    fmapFDE :: (FDEConvertible f a, FDEConvertible f b) => (a -> b) -> FunctorDExpr f a -> FunctorDExpr f b

    
-- | 'FDEDistributive' allows you to distribute a 'Functor'-like structure
-- over 'FunctorDExpr'
class (FDECompatible fd) => FDEDistributive (fd :: Type -> Type) where
    distributeFDE :: (FDEConvertible fd (fa a)) => fd (FunctorDExpr fa a) -> FunctorDExpr fd (fa a)

-- | 'FDETraversable' allows you to run  'sequenceA'
-- over a 'FunctorDExpr'
class (FDECompatible fd) => FDETraversable (fd) where
    sequenceFDE :: (FDEConvertible fd (fa a)) => FunctorDExpr fd (fa a) -> fd (FunctorDExpr fa a)



-- | 'FNotWrapped' is a wrapper that just passes through 'fmap' and
--  'patch' operations. It is basically 'Identity' for 'FunctorDExpr'
newtype FNotWrapped a = FNotWrapped a
newtype FNotWrappedD a = FNotWrappedD (PatchDelta a)

instance Functor FNotWrapped where
    fmap f (FNotWrapped a) = FNotWrapped (f a)

--instance Functor FNotWrappedD where
    --fmap f (FNotWrappedD a) = FNotWrappedD (f a)

instance Foldable FNotWrapped where
    foldMap f (FNotWrapped a) = f a
    
--instance Foldable FNotWrappedD where
    --foldMap f (FNotWrappedD a) = f a
        
instance FDECompatible FNotWrapped where
    type FDEConstraint FNotWrapped a = (Patchable (FNotWrapped a))

    toFDE (ZDV a da) = FDE a da
    fromFDE (FDE a da) = ZDV a da
    fromFD (FNotWrappedD a) = FNotWrappedD a
    toFD (FNotWrappedD a) = FNotWrappedD a

--instance FDEFunctor FNotWrapped where
    --fmapFDE f (FDE a da) = FDE (fmap f a) (fmap f da)

type instance FunctorDelta (FNotWrapped) = FNotWrappedD
type instance PatchDelta (FNotWrapped a) = FNotWrappedD a

instance (PatchInstance (PatchDelta a)) => PatchInstance (FNotWrappedD a) where
    mergepatches (FNotWrappedD da) (FNotWrappedD da') = FNotWrappedD (mergepatches da da')
    nopatch = FNotWrappedD nopatch

instance (Patchable a) => Patchable (FNotWrapped a) where
    patch (FNotWrapped a) (FNotWrappedD da) = FNotWrapped (patch a da)
    changes (FNotWrapped a) (FNotWrapped a') = FNotWrappedD (changes a a')


--
-- Functions and typeclasses for FunctorDExpr
--

-- | Apply the patch stored in a FunctorDExpr
fdeApplyPatch :: (FDEConvertible f a, FDECompatible f, Patchable (f a)) => FunctorDExpr f a -> (f a)
fdeApplyPatch v = zdApplyPatch $ fromFDE v
