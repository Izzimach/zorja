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
-- ListX, basically a list that supports FunctorDelta
--

newtype ListX f a = ListX [f a]
    deriving (Eq, Show)

data ListXF a x = 
      ConsX a x 
    | NilX
    deriving (Eq, Show)

instance (Functor f) => Functor (ListX f) where
    fmap f (ListX as) = ListX (fmap (fmap f) as) 

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

instance (Applicative f) => Applicative (ListX f) where
    pure x = ListX [pure x]
    (ListX a) <*> (ListX b) = ListX (liftA2 (<*>) a b)

instance (Foldable f) => Foldable (ListX f) where
    foldMap f (ListX as) = foldMap (foldMap f) as

instance (Traversable f) => Traversable (ListX f) where
    traverse g (ListX as) = ListX <$> (traverse (traverse g) as)
    
type instance (PatchDelta (ListX f a)) = (ListX (FunctorDelta f) a)
type instance FunctorDelta (ListX f) = ListX (FunctorDelta f)

-- |Algebra for mappending 'FunctorDExpr' vaues together.
-- 'cata mappendFDE' is basically foldMap for FunctorDExpr
mappendFDE :: (Monoid (FunctorDExpr f a)) => 
    ListXF (FunctorDExpr f a) (FunctorDExpr f a) -> (FunctorDExpr f a)
mappendFDE NilX = mempty
mappendFDE (ConsX a b) = a <> b

-- | We implement ListX as a free Monoid
instance Semigroup (ListX f a) where
    (ListX a) <> (ListX b) = ListX $ a <> b

-- | We implement ListX as a free Monoid
instance Monoid (ListX f a) where
    mempty = ListX []

instance (PatchInstance (f a)) => PatchInstance (ListX f a) where
    mergepatches (ListX a) (ListX b) = ListX $ zipWith mergepatches a b
    nopatch = ListX $ repeat nopatch

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

instance (Functor f) => FDECompatible (ListX f) where
    type FDEConstraint (ListX f) a = (FDECompatible f, FDEConstraint f a, Patchable (f a), PatchInstance (ListX (FunctorDelta f) a))
    toFDE z = let (v,dv) = zdEval z
              in FDE v dv
    fromFDE (FDE v dv) = ZDV v dv
    toFD (ListX a) = ListX a
    fromFD (ListX a) = ListX a

instance FDEDistributive ListX where
    distributeFDE :: FunctorDExpr (ListX f) a -> ListX (FunctorDExpr f) a
    distributeFDE (FDE (ListX as) (ListX das)) = ListX $ zipWith FDE as das

instance (FDETraversable f) => FDETraversable (ListX f) where
    sequenceFDE :: FunctorDExpr (ListX f) (g a) -> ListX f (FunctorDExpr g a)
    sequenceFDE (FDE (ListX as) (ListX das)) = ListX $ fmap sequenceFDE $ zipWith FDE as das

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
