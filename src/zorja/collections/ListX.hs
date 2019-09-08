{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Collections.ListX where

import Control.Applicative

import Data.Functor.Foldable

import Zorja.Patchable
import Zorja.ZHOAS
import Zorja.FunctorDExpr

--
-- | ListX, basically a list that supports FunctorDelta
--  The 'ListX' type is meant for experimental and testing
--  purposes, since it has several drawbacks:
--  - The delta cannot represent adding or removing elements from the list
--  - To rearrange or swap elements you basically have to destroy the elements
--    and rebuild them in their new positions.
--

newtype ListX f a = ListX [f a]
    deriving (Eq, Show)
    deriving (Semigroup, Monoid) via [f a]

instance (Functor f) => Functor (ListX f) where
    fmap f (ListX as) = ListX (fmap (fmap f) as) 

instance (Applicative f) => Applicative (ListX f) where
    pure x = ListX [pure x]
    (ListX a) <*> (ListX b) = ListX (liftA2 (<*>) a b)

instance (Foldable f) => Foldable (ListX f) where
    foldMap f (ListX as) = foldMap (foldMap f) as

instance (Traversable f) => Traversable (ListX f) where
    traverse g (ListX as) = ListX <$> (traverse (traverse g) as)


instance (PatchInstance (f a)) => PatchInstance (ListX f a) where
    mergepatches (ListX a) (ListX b) = ListX $ zipWith mergepatches a b
    nopatch = ListX $ repeat nopatch



-- | Non-recursive functor representation of ListX for recursion-schemes
data ListXF a x = 
    ConsX a x 
    | NilX
    deriving (Eq, Show)
    
instance Functor (ListXF a) where
    fmap f (ConsX a b) = ConsX a (f b)
    fmap _f NilX        = NilX

type instance Base (ListX f a) = ListXF (f a)
    
instance Recursive (ListX f a) where
    project (ListX [])     = NilX
    project (ListX (x:xs)) = ConsX x (ListX xs)

instance Corecursive (ListX f a) where
    embed (ConsX x (ListX xs)) = ListX (x:xs)
    embed NilX                 = ListX []

type instance (PatchDelta (ListX f a)) = (ListX (FunctorDelta f) a)
type instance FunctorDelta (ListX f) = ListX (FunctorDelta f)

instance (Functor f) => FDECompatible (ListX f) where
    type FDEConstraint (ListX f) a = (FDECompatible f, FDEConstraint f a, Patchable (f a), PatchInstance (ListX (FunctorDelta f) a))
    toFDE z = let (v,dv) = zdEval z
              in FDE v dv
    fromFDE (FDE v dv) = ZDV v dv
    --toFD (ListX a) = ListX a
    --fromFD (ListX a) = ListX a

{-instance (FDEDistributive f) => FDEDistributive (ListX f) where
    --distributeFDE :: (FDEConstraint (ListX f) a) => ListX f (FunctorDExpr fa a) -> FunctorDExpr (ListX f) (fa a)
    distributeFDE (ListX fdes) = FDE (ListX (fmap getA fdes')) (ListX (fmap getDA fdes'))
        where
            fdes' = fmap distributeFDE fdes
            getA (FDE a _) = a
            getDA (FDE _ da) = da

instance (FDETraversable f) => FDETraversable (ListX f) where
    --sequenceFDE :: (FDEConstraint (ListX f) (g a)) => FunctorDExpr (ListX f) (g a) -> ListX f (FunctorDExpr g a)
    sequenceFDE (FDE (ListX as) (ListX das)) = ListX $ fmap sequenceFDE $ zipWith FDE as das
-}

instance (Functor f, Functor (FunctorDelta f)) => FDEFunctor (ListX f) where
    fmapFDE f (FDE a da) = FDE (fmap f a) (fmapFD f da)
    fmapFD f (ListX fa) = ListX (fmap (fmap f) fa)

instance (FDECompatible f, FDEConstraint f a, PatchInstance (ListX (FunctorDelta f) a), Patchable (f a)) 
    => Patchable (ListX f a) where
    patch (ListX a) (ListX da) = ListX $ zipWith fpatch a da
        where
            fpatch v dv = fdeApplyPatch (FDE v dv)

    changes (ListX a) (ListX a') = ListX $ zipWith fchanges a a'
        where
            fchanges v v' = let dv = changes v v'
                                -- convert from PatchDelta to FunctorDelta
                                (FDE _da dfa) = toFDE (ZDV v dv)
                            in dfa

-- |Algebra for mappending 'FunctorDExpr' vaues together.
-- 'cata mappendFDE' is basically foldMap for FunctorDExpr
mappendFDE :: (Monoid (FunctorDExpr f a)) => 
    ListXF (FunctorDExpr f a) (FunctorDExpr f a) -> (FunctorDExpr f a)
mappendFDE NilX = mempty
mappendFDE (ConsX a b) = a <> b

-- coalgebra for ListX  unfolding
coalgListXFDE :: FunctorDExpr (ListX f) a -> ListXF (FunctorDExpr f a) (FunctorDExpr (ListX f) a)
coalgListXFDE (FDE (ListX a) (ListX b)) =
    case (a,b) of
        ([],_) -> NilX
        (_,[]) -> NilX
        (x:xs, dx:dxs) -> ConsX (FDE x dx) (FDE (ListX xs) (ListX dxs))

mergeListXFDE :: (Monoid (FunctorDExpr f a)) => ListXF (FunctorDExpr f a) (FunctorDExpr f a) -> FunctorDExpr f a
mergeListXFDE NilX = mempty
mergeListXFDE (ConsX a b) = a <> b
