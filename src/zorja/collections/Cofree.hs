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

module Zorja.Collections.Cofree where
    
import Data.Functor.Foldable
import Data.Semigroup
import Data.Distributive
import Data.Kind (Type, Constraint)

import Control.Applicative

import Zorja.Patchable
import Zorja.ZHOAS

data FunctorDExpr f a = FDE (f a) ((FunctorDelta f) a)


class FDECompatible f where
    type FDEConstraint f a :: Constraint
    toFDE :: (FDEConstraint f a) => ZDExpr (f a) -> FunctorDExpr f a
    fromFDE :: (FDEConstraint f a) => FunctorDExpr f a -> ZDExpr (f a)

fdeApplyPatch :: (FDECompatible f, FDEConstraint f a, Patchable (f a)) => FunctorDExpr f a -> f a
fdeApplyPatch v = zdApplyPatch $ fromFDE v

class FDEDistributive (fd :: (* -> *) -> * -> *) where
    distributeFDE :: FunctorDExpr (fd fx) x -> fd (FunctorDExpr fx) x

class FDETraversable (fd :: Type -> Type) where
    traverseFDE :: FunctorDExpr fd (fx x) -> fd (FunctorDExpr fx x)

instance (Semigroup a) => Semigroup (FunctorDExpr ReplaceOnly a) where
    (FDE (ReplaceOnly a) (Replacing da)) <> (FDE (ReplaceOnly b) (Replacing db)) =
        let c = case (getOption da, getOption db) of
                    (Nothing, Nothing) -> Option Nothing
                    (Just (Last da'), Nothing) -> (Option (Just (Last (da' <> b))))
                    (Nothing, Just (Last db')) -> (Option (Just (Last (a <> db'))))
                    (Just (Last da'), Just (Last db')) -> Option (Just (Last (da' <> db')))
        in
            FDE (ReplaceOnly $ a <> b) (Replacing c)

instance (Monoid a) => Monoid (FunctorDExpr ReplaceOnly a) where
    mempty = FDE mempty mempty

instance FDECompatible ReplaceOnly where
    type FDEConstraint ReplaceOnly a = (Eq a)
    toFDE z = let (v,dv) = zdEval z
              in FDE v dv
    fromFDE (FDE a da) = ZDV a da

-- algebra for mappending FunctorDExpr's
-- 'cata mappendFDE' is basically foldMap for FunctorDExpr
mappendFDE :: (Monoid (FunctorDExpr f a)) => 
    ListXF (FunctorDExpr f a) (FunctorDExpr f a) -> (FunctorDExpr f a)
mappendFDE NilX = mempty
mappendFDE (ConsX a b) = a <> b

instance (Show (f a), Show ((FunctorDelta f) a)) => Show (FunctorDExpr f a) where
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

--
-- ListX, basically a list that supports FunctorDelta
--

newtype ListX f a = ListX [f a]
    deriving (Eq, Show)

data ListXF a x = 
      ConsX a x 
    | NilX

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

-- | We implement ListX as a free Monoid
instance Semigroup (ListX f a) where
    (ListX a) <> (ListX b) = ListX $ a <> b

-- | We implement ListX as a free Monoid
instance Monoid (ListX f a) where
    mempty = ListX []

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

instance FDECompatible (ListX f) where
    type FDEConstraint (ListX f) a = (FDECompatible f, FDEConstraint f a, Patchable (f a), Monoid (FunctorDelta f a))
    toFDE z = let (v,dv) = zdEval z
              in FDE v dv
    fromFDE (FDE v dv) = ZDV v dv

instance FDEDistributive ListX where
    distributeFDE :: FunctorDExpr (ListX f) a -> ListX (FunctorDExpr f) a
    distributeFDE (FDE (ListX as) (ListX das)) = ListX $ zipWith FDE as das

instance (FDETraversable f) => FDETraversable (ListX f) where
    traverseFDE :: FunctorDExpr (ListX f) (g a) -> ListX f (FunctorDExpr g a)
    traverseFDE (FDE (ListX as) (ListX das)) = ListX $ fmap traverseFDE $ zipWith FDE as das

instance (FDECompatible f, FDEConstraint f a, Patchable (f a)) 
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

testList :: ListX ReplaceOnly (Sum Int)
testList = ListX [ReplaceOnly (Sum 3), ReplaceOnly (Sum 5)]

testListD :: PatchDelta (ListX ReplaceOnly (Sum Int))
--testListD :: ListXD Replacing (ListX ReplaceOnly Int)
testListD = ListX $ [Replacing (Option Nothing),
                     Replacing (Option (Just (Last (Sum (6::Int)) )))]

testListFDE :: FunctorDExpr (ListX ReplaceOnly) (Sum Int)
testListFDE = FDE testList testListD


-- try a hylomorphism...
-- - starting with a FunctorDExpr (ListX ReplaceOnly) (Sum Int)
-- - unfold into a ListX with coalListXFDE
-- - then fold up with mergeListXFDE
testListHylo :: FunctorDExpr ReplaceOnly (Sum Int)
testListHylo = hylo mergeListXFDE coalgListXFDE testListFDE

--
-- Cofree with FunctorDelta added
--

data CofD fb fa a = (fa a) :<< (fb (CofD fb fa a))

data CofDD fb fa a = (FunctorDelta fa a) :<# (FunctorDelta fb (CofD fb fa a))

instance (Eq a, Eq (fa a), forall x. Eq x => Eq (fb x)) => Eq (CofD fb fa a) where
    (a :<< as) == (b :<< bs)  =  (a == b) && (as == bs)

instance (Show (fa a), Show (fb (CofD fb fa a))) => Show (CofD fb fa a) where
    show (x :<< xs) = "(CofD " ++ show x ++ " :<< " ++ show xs ++ ")"
    
instance (Show (FunctorDelta fa a), Show (FunctorDelta fb (CofD fb fa a))) => Show (CofDD fb fa a) where
    show (x :<# xs) = "(CofDD " ++ show x ++ " :<< " ++ show xs ++ ")"
        
type instance PatchDelta (CofD fb fa a) = CofDD fb fa a --CofD fb (FunctorDelta fa) a
type instance FunctorDelta (CofD fb fa) = CofDD fb fa --CofD fb (FunctorDelta fa)

data CofDF fb fa a x = (fa a) :<= (fb x)

data CofDDF fb fa a x = (FunctorDelta fa a) :<=# (FunctorDelta fb x)

type instance PatchDelta (CofDF fb fa a x) = CofDDF fb fa a x--CofDF fb (FunctorDelta fa) a x
type instance FunctorDelta (CofDF fb fa a) = CofDDF fb fa a--CofDF fb (FunctorDelta fa) a

type instance Base (CofD fb fa a) = CofDF fb fa a

instance (Functor fb, Functor fa) => Functor (CofD fb fa) where
    fmap f (x :<< xs) = (fmap f x) :<< (fmap (fmap f) xs)

instance (Functor fb) => Functor (CofDF fb fa a) where
    fmap f (x :<= xs) = x :<= (fmap f xs)

instance (Functor fb) => Recursive (CofD fb fa a) where
    project (x :<< xs) = x :<= xs
instance (Functor fb) => Corecursive (CofD fb fa a) where
    embed (x :<= xs) = x :<< xs

instance (Semigroup (fa a), Applicative fb) => Semigroup (CofD fb fa a) where
    (a :<< as) <> (b :<< bs) = (a <> b) :<< (liftA2 (<>) as bs)

instance (Monoid (fa a), Monoid (fb (CofD fb fa a)), Applicative fb) => Monoid (CofD fb fa a) where
    mempty = mempty :<< mempty

instance (Semigroup (fa a),
          Semigroup (FunctorDelta fa a),
          Applicative fb,
          Applicative (FunctorDelta fb)) 
        => Semigroup (CofDD fb fa a) where
    (a :<# as) <> (b :<# bs) = (a <> b) :<# (liftA2 (<>) as bs)

instance (Monoid (fa a),
          Monoid (FunctorDelta fa a),
          Applicative fb,
          Applicative (FunctorDelta fb),
          Monoid (FunctorDelta fb (CofD fb fa a)))
        => Monoid (CofDD fb fa a) where
    mempty = mempty :<# mempty

instance (FDECompatible fa, FDECompatible fb) => FDECompatible (CofD fb fa) where
    type FDEConstraint (CofD fb fa) a = 
        (Patchable (fa a),
         Patchable (fb (CofD fb fa a)),
         Monoid (fb (CofD fb fa a)),
         Monoid (CofDD fb fa a),
         Monoid (fb (CofD fb (FunctorDelta fa) a)),
         Monoid (FunctorDelta fa a), 
         FDEConstraint fa a,
         FDEConstraint fb (CofD fb fa a),
         FunctorDelta fb (CofD fb fa a) ~ PatchDelta (fb (CofD fb fa a)),
         FunctorDelta fa a ~ PatchDelta (fa a))
    --toFDE :: ZDExpr (CofD fb fa a) -> FunctorDExpr (CofD fb fa) a
    toFDE z = let (v,dv) = zdEval z
              in (FDE v dv)
    --fromFDE :: FunctorDExpr (CofD fb fa) a -> ZDExpr (CofD fb fa a)
    fromFDE (FDE a da) = ZDV a da


instance (Functor fb, FDETraversable fb) => FDEDistributive (CofD fb) where 
    distributeFDE :: FunctorDExpr (CofD fb fa) a -> CofD fb (FunctorDExpr fa) a
    distributeFDE (FDE x dx) =
        let (a  :<< as)  = x
            (da :<# das) = dx
        in
            (FDE a da) :<< (fmap distributeFDE (traverseFDE (FDE as das)))

instance (FDECompatible fa,
          FDECompatible fb,
          FDEConstraint fa a,
          FDEConstraint fb (CofD fb fa a),
          FunctorDelta fa a ~ PatchDelta (fa a),
          FunctorDelta fb (CofD fb fa a) ~ PatchDelta (fb (CofD fb fa a)),
          Patchable (fa a),
          Patchable (fb (CofD fb fa a)),
          Monoid (CofDD fb fa a)) =>
              Patchable (CofD fb fa a) where
    patch (a :<< as) (da :<# das) =
        let b  = (fdeApplyPatch (FDE a da)) 
            bs = (fdeApplyPatch (FDE as das))
        in
            b :<< bs

    changes (a :<< as) (a' :<< as') = (changes a a') :<# (changes as as')


combineCofreeFDE ::
    (FDETraversable (fb x)) =>
        FunctorDExpr (CofD (fb x) fa) a -> 
        CofDF (fb x) (FunctorDExpr fa) a (FunctorDExpr (CofD (fb x) fa) a)
combineCofreeFDE (FDE (a :<< as) (da :<# das)) =
    (FDE a da) :<= (traverseFDE (FDE as das))


--foldCofreeFDE ::    
                        
testTree :: CofD (ListX ReplaceOnly) ReplaceOnly (Sum Int)
testTree = (ReplaceOnly 3)
               :<<
               ListX [ReplaceOnly $ (ReplaceOnly (Sum 4)) :<< ListX [], 
                      ReplaceOnly $ (ReplaceOnly (Sum 5)) :<< ListX []]

testTreeD :: PatchDelta (CofD (ListX ReplaceOnly) ReplaceOnly (Sum Int))
testTreeD = let nochange  = Replacing $ Option $ Nothing
                leaf x    = Replacing $ Option $ Just $ Last $ (ReplaceOnly x) :<< ListX []
                emptyleaf = Replacing $ Option $ Nothing
            in
                nochange :<# ListX [leaf (Sum 9),
                                    emptyleaf]

testTreeFDE :: FunctorDExpr (CofD (ListX ReplaceOnly) ReplaceOnly) (Sum Int)
testTreeFDE = FDE testTree testTreeD

testTreeZD :: ZDExpr (CofD (ListX ReplaceOnly) ReplaceOnly (Sum Int))
testTreeZD = fromFDE testTreeFDE
