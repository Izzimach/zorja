{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Collections.Cofree (
    CofD(..),
    CofDD(..),
    coalgCofreeFDE,
    foldMapCofreeFDE
    ) where
    
import Data.Functor.Foldable
import Data.Functor.Identity
import Data.Kind
import Data.Semigroup

import Control.Applicative

import Zorja.Patchable
import Zorja.Primitives
import Zorja.ZHOAS
import Zorja.FunctorDExpr
import Zorja.Collections.ListX

--
-- | A version of 'Cofree' that can be used with
--   'FunctorDelta' and 'FunctorDExpr'

data CofD fb fa a = (fa a) :<< (fb (CofD fb fa) a)

data CofDD fb fa a = (FunctorDelta fa a) :<# (FunctorDelta (fb (CofD fb fa)) a)

instance (Eq a, Eq (fa a), Eq (fb (CofD fb fa) a)) => Eq (CofD fb fa a) where
    (a :<< as) == (b :<< bs)  =  (a == b) && (as == bs)

instance (Show (fa a), Show (fb (CofD fb fa) a)) => Show (CofD fb fa a) where
    show (x :<< xs) = "(CofD " ++ show x ++ " :<< " ++ show xs ++ ")"
    
instance (Show (FunctorDelta fa a), Show (FunctorDelta (fb (CofD fb fa)) a)) => Show (CofDD fb fa a) where
    show (x :<# xs) = "(CofDD " ++ show x ++ " :<< " ++ show xs ++ ")"
        
type instance PatchDelta (CofD fb fa a) = CofDD fb fa a --CofD fb (FunctorDelta fa) a
type instance FunctorDelta (CofD fb fa) = CofDD fb fa --CofD fb (FunctorDelta fa)

data CofDF fb fa a x = (fa a) :<= (fb fa x)

data CofDDF fb fa a x = (FunctorDelta fa a) :<=# (FunctorDelta (fb fa) x)

type instance PatchDelta (CofDF fb fa a x) = CofDDF fb fa a x --CofDF fb (FunctorDelta fa) a x
type instance FunctorDelta (CofDF fb fa a ) = CofDDF fb fa a --CofDF fb (FunctorDelta fa) a

type instance Base (CofD fb fa a) = CofDF fb fa a

instance (Functor (fb (CofD fb fa)), Functor fa) => Functor (CofD fb fa) where
    fmap f (x :<< xs) = (fmap f x) :<< (fmap (fmap f) xs)

instance (Functor (fb (CofD fb fa))) => Functor (CofDF fb fa a) where
    fmap f (x :<= xs) = x :<= (fmap f xs)

instance (Functor (fb (CofD fb fa))) => Recursive (CofD fb fa a) where
    project (x :<< xs) = x :<= xs

instance (Functor (fb (CofD fb fa))) => Corecursive (CofD fb fa a) where
    embed (x :<= xs) = x :<< xs

instance (Semigroup (fa a), Applicative (fb (CofD fb fa))) => Semigroup (CofD fb fa a) where
    (a :<< as) <> (b :<< bs) = (a <> b) :<< (liftA2 (<>) as bs)

instance (Monoid (fa a), Monoid (fb (CofD fb fa) a), Applicative (fb (CofD fb fa))) => Monoid (CofD fb fa a) where
    mempty = mempty :<< mempty

instance (Semigroup (fa a),
          Semigroup (FunctorDelta fa a),
          Applicative (fb (CofDD fb fa)),
          Applicative (FunctorDelta (fb (CofDD fb fa))))
        => Semigroup (CofDD fb fa a) where
    (a :<# as) <> (b :<# bs) = (a <> b) :<# (liftA2 (<>) as bs)

instance (Monoid (fa a),
          Monoid (FunctorDelta fa a),
          Applicative (fb (CofD fb fa)),
          Applicative (FunctorDelta (fb (CofD fb fa))),
          Monoid (FunctorDelta (fb (CofD fb fa)) a))
        => Monoid (CofDD fb fa a) where
    mempty = mempty :<# mempty

instance (PatchInstance (FunctorDelta fa a),
          PatchInstance (FunctorDelta (fb (CofD fb fa)) a))
        => PatchInstance (CofDD fb fa a) where
    mergepatches (a1 :<# as1) (a2 :<# as2) = 
        (mergepatches a1 a2) :<# (mergepatches as1 as2)
    nopatch = nopatch :<# nopatch

instance (FDECompatible fa, FDECompatible (fb (CofD fb fa))) => FDECompatible (CofD fb fa) where
    type FDEConstraint (CofD fb fa) a = 
        (Patchable (fa a),
         Patchable ((fb (CofD fb fa)) a),
         Monoid ((fb (CofD fb fa)) a),
         PatchInstance (FunctorDelta (fb (CofD fb fa)) a),
         Monoid (fb (CofD fb (FunctorDelta fa)) a),
         Monoid (FunctorDelta fa a), 
         FDEConstraint fa a,
         FDEConstraint (fb (CofD fb fa)) a)
    --toFDE :: ZDExpr (CofD fb fa a) -> FunctorDExpr (CofD fb fa) a
    toFDE z = let (v,dv) = zdEval z
              in (FDE v dv)
    --fromFDE :: FunctorDExpr (CofD fb fa) a -> ZDExpr (CofD fb fa a)
    fromFDE (FDE a da) = ZDV a da
    toFD z = z
    fromFD z = z

instance (Functor (fb (CofD fb fa)), 
          FDEDistributive (fb (CofD fb fa)),
          FDEDistributive fa) => FDEDistributive (CofD fb fa) where 
    --distributeFDE :: (FDEConstraint (CofD fb fa) (fx x)) => CofD fb fa (FunctorDExpr fx x) -> FunctorDExpr (CofD fb fa) (fx x)
    distributeFDE (a :<< as) = 
        let (FDE v dv) = distributeFDE a
            (FDE x xs) = distributeFDE $ fmap distributeFDE as
        in
            FDE (v :<< x) (dv :<# xs)

instance (Applicative fa, Applicative (fb (CofD fb fa)), FDETraversable fa, FDETraversable (fb (CofD fb fa))) => FDETraversable (CofD fb fa) where
    --sequenceFDE :: (FDEConstraint (CofD fb fa) (fx x)) => FunctorDExpr (CofD fb fa) (fx x) -> CofD fb fa (FunctorDExpr fx x)
    sequenceFDE (FDE x dx) =
        let (a :<< as) = x
            (da :<# das) = dx
            x' = sequenceFDE (FDE a da)
            dx' = sequenceFDE (FDE as das)
        in
            -- wha
            x' :<< (fmap sequenceFDE dx')


instance (
            FDECompatible fa,
            FDEConvertible fa a,
            Patchable (fa a),
            PatchInstance (FunctorDelta fa a),
            FDECompatible (fb (CofD fb fa)),
            FDEConvertible (fb (CofD fb fa)) a,
            Patchable ((fb (CofD fb fa)) a),
            PatchInstance (FunctorDelta (fb (CofD fb fa)) a)) =>
              Patchable (CofD fb fa a) where
    patch (a :<< as) (da :<# das) = 
        let b  = (fdeApplyPatch (FDE a da)) 
            bs = (fdeApplyPatch (FDE as das))
        in
            b :<< bs

    changes (a :<< as) (a' :<< as') = (toFD (changes a a')) :<# (toFD (changes as as'))

--
-- | Unfold @FunctorDExpr CofD@ into a 'CofDF'. Useful as a coalgebra for
--   ana- and hylo- morphisms.
--
coalgCofreeFDE ::
    (FDETraversable (fb (CofD fb fa)),
     FDEConvertible (fb (CofD fb fa)) a) =>
        FunctorDExpr (CofD fb fa) a -> 
        CofDF fb (FunctorDExpr fa) a (FunctorDExpr (CofD fb fa) a)
coalgCofreeFDE (FDE (a :<< as) (da :<# das)) =
    (FDE a da) :<= (sequenceFDE (FDE as das))


-- | Fold up CofDF using mappend
foldMapCofreeFDE ::
    (Semigroup (FunctorDExpr fa a),
     Monoid (FunctorDExpr fa a),
     Foldable (fb (CofD fb fa)),
     FDETraversable (fb (CofD fb fa)),
     FDEConvertible (fb (CofD fb fa)) a) =>
        CofDF fb (FunctorDExpr fa) a (FunctorDExpr fa a) ->
        FunctorDExpr fa a
foldMapCofreeFDE (fa :<= vs) = fa <> (foldMap id vs)

--foldCofreeFDE ::    
                        
testTree :: CofD (ListX) ReplaceOnly (Sum Int)
testTree = (ReplaceOnly 3)
               :<<
               ListX [FNotWrapped $ (ReplaceOnly (Sum 4)) :<< ListX [], 
                      FNotWrapped $ (ReplaceOnly (Sum 5)) :<< ListX []]

testTreeD :: PatchDelta  (CofD (ListX) ReplaceOnly (Sum Int))
testTreeD = let nochange  = Replacing $ Nothing
                leaf x    = FNotWrappedD $ (Replacing $ Just x) :<# ListX []
                emptyleaf = FNotWrappedD $ nopatch
            in
                nochange :<# ListX [leaf (Sum (9 :: Int)),
                                    emptyleaf]

testTreeFDE :: FunctorDExpr (CofD (ListX) ReplaceOnly) (Sum Int)
testTreeFDE = FDE testTree testTreeD

testTreeZD :: ZDExpr (CofD (ListX) ReplaceOnly (Sum Int))
testTreeZD = fromFDE $ testTreeFDE
