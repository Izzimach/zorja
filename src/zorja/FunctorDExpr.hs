{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.FunctorDExpr where

import Data.Distributive
import Data.Kind (Type, Constraint)

import Zorja.Patchable
import Zorja.ZHOAS
    
--
-- |'FunctorDExpr' is a 'ZDExpr' where both 'a' and 'da' can be expressed as
-- functors. You can switch between the two using 'toFDE' and 'fromFDE'

data FunctorDExpr f a = FDE (f a) (FunctorDelta f a)

-- |'FDECompatible' is for 'Functor's (and their associated 'FunctorDelta')
-- that can be converted between 'ZDExpr' 'FunctorDExpr'

class FDECompatible (f :: Type -> Type) where
    type FDEConstraint f a :: Constraint

    toFDE :: (FDEConstraint f a) => ZDExpr (f a) -> FunctorDExpr f a
    fromFDE :: (FDEConstraint f a) => FunctorDExpr f a -> ZDExpr (f a)

    toFD :: (FDEConstraint f a) => PatchDelta (f a) -> FunctorDelta f a
    fromFD :: (FDEConstraint f a) => FunctorDelta f a -> PatchDelta (f a)

-- | A 'FDFunctor' allows you to take a function normally used to 'fmap'
--  on a functor 'fd' and instead apply it to a
-- 'FunctorDelta fd' or 'FunctorDExpr fd'
class (Functor f, FDECompatible f) => FDEFunctor (f :: Type -> Type) where
    fmapFD :: (a -> b) -> FunctorDelta f a -> FunctorDelta f b
    fmapFDE :: (a -> b) -> FunctorDExpr f a -> FunctorDExpr f b


-- | 'FDEDistributive' allows you to distribute a 'Functor'-like structure
-- over 'FunctorDExpr'
class (FDECompatible fd) => FDEDistributive (fd :: Type -> Type) where
    distributeFDE :: (FDEConstraint fd (fa a)) => fd (FunctorDExpr fa a) -> FunctorDExpr fd (fa a)

-- | 'FDETraversable' allows you to run 'sequenceA'
-- over a 'FunctorDExpr'
class (FDECompatible fd) => FDETraversable (fd) where
    sequenceFDE :: (FDEConstraint fd (fa a)) => FunctorDExpr fd (fa a) -> fd (FunctorDExpr fa a)


--
-- Functions and typeclasses for FunctorDExpr
--

-- | Apply the patch stored in a FunctorDExpr
fdeApplyPatch :: (FDEConstraint f a, FDECompatible f, Patchable (f a)) => FunctorDExpr f a -> f a
fdeApplyPatch v = zdApplyPatch $ fromFDE v


instance (Show (f a), Show (FunctorDelta f a)) => Show (FunctorDExpr f a) where
    show (FDE fa dfa) = "(FDE " ++ show fa ++ "," ++ show dfa ++ ")"

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
