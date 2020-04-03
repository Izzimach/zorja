{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.FunctorDExpr where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Env
import Control.Comonad.Store
import Control.Comonad.Cofree

import Data.Functor.Foldable
import Data.Distributive
import Data.Kind (Type)
import Data.Proxy

import Fcf.Core

import Zorja.Patchable
import Zorja.ZHOAS

-- | Things of the  `ZFunctor` can represent either a value
-- of a delta of that value. They take an extra type 'ILCOrder'
-- to distinguish between the two. The combined value/delta is here
-- called 'Jet' based on some of Phil Freeman's posts about Incremental
-- Lambda Calculus in Purescript
data ILCOrder = HKTValue | HKTDelta | HKTJet

-- | A `ZFunctor' can work with values or deltas.
-- This allows us to talk about both value and deltas
-- in a single expression. The decision about whether we're talking about
-- values or deltas is deferred until later.
type ZFunctor = ILCOrder -> Type -> Type

-- | An 'SFunctor' wraps a 'ZFunctor' to produce another 'ZFunctor'.
-- Same as @ZFunctor -> ILCOrder -> Type -> Type@
-- Type sig for a typical SFunctor is
--  @SFunc :: (f :: ZFunctor) (d : ILCOrder) a@
type SFunctor = ZFunctor -> ZFunctor

-- | 'ZDExpr' as a 'ZFunctor'
newtype SDExpr (f :: ZFunctor) d a = SDE { unSDE :: (ZDExpr (f 'HKTValue a)) }


-- | A ZFunctor that's just the value itself with no wrapper.
type ZNoWrap (d :: ILCOrder) a = a

-- | A way to combine/break apart value/delta pairs
class (forall a. Patchable (f 'HKTValue a), forall a. PatchInstance (f 'HKTDelta a)) => ZJetify (f :: ZFunctor) where
    toILCDelta :: f 'HKTDelta a -> ILCDelta (f 'HKTValue a)
    fromILCDelta :: (ILCDelta (f 'HKTValue a)) -> f 'HKTDelta a
    toZDExpr :: f 'HKTJet a -> ZDExpr (f 'HKTValue a)
    fromZDExpr :: ZDExpr (f 'HKTValue a) -> f 'HKTJet a
    jetZip :: (f 'HKTValue a, f 'HKTDelta a) -> f 'HKTJet a
    jetUnzip :: f 'HKTJet a -> (f 'HKTValue a, f 'HKTDelta a) 

class (ZJetify f) => ZJetDist (f :: ZFunctor) where
    distZJet :: (Patchable a) => ZDExpr (f 'HKTValue a) -> f 'HKTValue (ZDExpr a)
    traverseZJet :: (Patchable a) => f 'HKTValue (ZDExpr a) -> ZDExpr (f 'HKTValue a)

-- | ZJetify for recursive ZFunctors
class ZJetify2 (s :: ZFunctor) where
    jetZip2 :: (ZJetify (f s)) => (s 'HKTValue (f s 'HKTValue a), s 'HKTDelta (f s 'HKTDelta a)) -> s 'HKTJet (f s 'HKTJet a)
    jetUnzip2 :: (ZJetify (f s)) => s 'HKTJet (f s 'HKTJet a) -> (s 'HKTValue (f s 'HKTValue a), s 'HKTDelta (f s 'HKTDelta a))


-- | ZJetDist for 'SFunctor'
class SJetDist (s :: SFunctor) where
    extractSJet :: (ZJetify f) => SDExpr (s f) 'HKTValue a -> s (SDExpr f) 'HKTValue a
    injectSJet :: (ZJetify f) => s (SDExpr f) 'HKTValue a -> SDExpr (s f) 'HKTValue a

--
-- | Identity as a `ZFunctor`.
--   Not too useful since patching is not clearly defined. If you're considering
--   using 'ZIdentity' you might want to consider using 'ZReplaceOnly' which
--   has a clearly defined meaning for 'patch'
data family ZIdentity (d :: ILCOrder) a

data instance ZIdentity 'HKTValue a = ZIdentity a
    deriving (Eq, Show)
data instance ZIdentity 'HKTDelta a = ZDIdentity a
    deriving (Eq, Show)
data instance ZIdentity 'HKTJet a = ZJet a a
    deriving (Eq, Show)

type instance ILCDelta (ZIdentity 'HKTValue a) = ZIdentity 'HKTDelta a

instance Functor (ZIdentity 'HKTValue) where
    fmap f (ZIdentity a) = ZIdentity (f a)

instance Functor (ZIdentity 'HKTDelta) where
    fmap f (ZDIdentity a) = ZDIdentity (f a)

instance Functor (ZIdentity 'HKTJet) where
    fmap f (ZJet a b) = ZJet (f a) (f b)

-- | 'ReplaceOnly' as a 'ZFunctor'
data family ZReplaceOnly (d :: ILCOrder) a

data instance ZReplaceOnly 'HKTValue a = ZReplaceValue a
    deriving (Eq, Show)
data instance ZReplaceOnly 'HKTDelta a = ZReplaceDelta (Maybe a)
    deriving (Eq, Show)
data instance ZReplaceOnly 'HKTJet a = ZReplaceJet a (Maybe a)
    deriving (Eq, Show)

type instance ILCDelta (ZReplaceOnly 'HKTValue a) = ZReplaceOnly 'HKTDelta a

instance ZJetify ZReplaceOnly where
    toILCDelta a = a
    fromILCDelta a = a
    toZDExpr j = (uncurry ZDV) $ jetUnzip j
    fromZDExpr z = jetZip $ zdEval z
    jetZip (ZReplaceValue a, ZReplaceDelta da) = ZReplaceJet a da
    jetUnzip (ZReplaceJet a da) = (ZReplaceValue a, ZReplaceDelta da)

instance ZJetDist ZReplaceOnly where
    -- ? not sure this is possible
    distZJet = undefined
    traverseZJet = undefined

instance PatchInstance (ZReplaceOnly 'HKTDelta a) where
    (ZReplaceDelta _) <^< (ZReplaceDelta (Just b)) = ZReplaceDelta (Just b)
    (ZReplaceDelta a) <^< (ZReplaceDelta Nothing) = ZReplaceDelta a
    noPatch = ZReplaceDelta Nothing

instance Patchable (ZReplaceOnly 'HKTValue a) where
    patch a (ZReplaceDelta Nothing)  = a
    patch _ (ZReplaceDelta (Just b)) = ZReplaceValue b
    changes (ZReplaceValue a) (ZReplaceValue b) = ZReplaceDelta (Just b)

instance Functor (ZReplaceOnly 'HKTValue) where
    fmap f (ZReplaceValue a) = ZReplaceValue (f a)

instance Functor (ZReplaceOnly 'HKTDelta) where
    fmap f (ZReplaceDelta a) = ZReplaceDelta (fmap f a)

--
-- ZList
--

-- | List as a `ZFunctor`
newtype ZList (f :: ZFunctor) (d :: ILCOrder) a = ZList [f d a]
    deriving (Eq, Show)

data ZListF (f :: ZFunctor) (d :: ILCOrder) a x =
      ZNil 
    | ZCons (f d a) x
    deriving (Eq, Show)

type instance ILCDelta (ZList f 'HKTValue a) = ZList f 'HKTDelta a

type instance Base (ZList f d a) = ZListF f d a

instance (Functor (f d)) => Functor (ZList f d) where
    fmap f (ZList xs) = ZList (fmap (fmap f) xs)

instance (Functor (f d)) => Functor (ZListF f d a) where
    fmap _ ZNil        = ZNil
    fmap f (ZCons a x) = ZCons a (f x)

instance (Functor (f d)) => Recursive (ZList f d a) where
    project (ZList [])     = ZNil
    project (ZList (x:xs)) = ZCons x (ZList xs)

instance (Functor (f d)) => Corecursive (ZList f d a) where
    embed ZNil                 = ZList []
    embed (ZCons x (ZList xs)) = ZList (x:xs)

instance (PatchInstance (f 'HKTDelta a)) => PatchInstance (ZList f 'HKTDelta a) where
    (ZList das) <^< (ZList dbs) = ZList $ zipWith (<^<) das dbs
    noPatch = ZList []



instance (ZJetify f, PatchInstance (f 'HKTDelta a)) => (Patchable (ZList f 'HKTValue a)) where
    -- not a great solution as it discards values if the list of deltas is too short
    patch (ZList as) (ZList das) = ZList (zipWith (\a da -> patch a (toILCDelta da)) as das)
    changes (ZList as) (ZList bs) = ZList (zipWith (\a b -> fromILCDelta $ changes a b) as bs)

instance (ZJetify f) => ZJetify (ZList f) where
    toILCDelta (ZList as) = ZList as
    fromILCDelta (ZList as) = ZList as
    toZDExpr :: ZList f 'HKTJet a -> ZDExpr (ZList f 'HKTValue a)
    toZDExpr zs = (uncurry ZDV) $ jetUnzip zs
    fromZDExpr :: ZDExpr (ZList f 'HKTValue a) -> ZList f 'HKTJet a
    fromZDExpr z = jetZip $ zdEval z
    jetZip :: (ZList f 'HKTValue a, ZList f 'HKTDelta a) -> ZList f 'HKTJet a
    jetZip (ZList a, ZList da) = ZList (zipWith (curry jetZip) a da)
    jetUnzip :: ZList f 'HKTJet a -> (ZList f 'HKTValue a, ZList f 'HKTDelta a) 
    jetUnzip (ZList zs) = let (a,da) = unzip $ fmap jetUnzip zs
                          in (ZList a, ZList da)

{-
instance (ZJetify f, ZJetDist f, forall a. (Patchable (f 'HKTValue a), PatchInstance (f 'HKTDelta a))) => ZJetDist (ZList f) where
    extractZJet :: ZDExpr (ZList f 'HKTValue a) -> ZList f 'HKTValue (ZDExpr a)
    extractZJet z = let (ZList a, ZList da) = zdEval z                     
                    in ZList $ fmap (extractZJet . toJet) $ zip a da
    injectZJet :: ZList f 'HKTValue (ZDExpr a) -> ZDExpr (ZList f 'HKTValue a)
    injectZJet (ZList z) = let (a,da) = unzip $ fmap (fromJet . injectZJet) z
                           in ZDV (ZList a) (ZList da)
-}

{-
instance SJetDist ZList where
    extractSJet (SDE z) = let (ZList a, ZList da) = zdEval z
                          in ZList $ zipWith (curry (SDE . toJet)) a da
    injectSJet (ZList s) = let (a,da) = unzip $ fmap (zdEval . unSDE) s
                           in SDE $ ZDV (ZList a) (ZList (fmap fromILC da))
-}

data ZMaybe (f :: ZFunctor) (d :: ILCOrder) a =
      ZJust (f d a)
    | ZNothing
    deriving (Eq, Show)

type instance ILCDelta (ZMaybe f 'HKTValue a) = ZMaybe f 'HKTDelta a

instance (Functor (f d)) => Functor (ZMaybe f d) where
    fmap f (ZJust a) = ZJust (fmap f a)
    fmap _ ZNothing = ZNothing





-- | Fix point (recursive) data structure for' ZFunctor' types.
newtype ZFix (f :: ZFunctor) (d :: ILCOrder) = ZFix (f d (ZFix f d))

type instance ILCDelta (ZFix f 'HKTValue) = ZFix f 'HKTDelta

type instance Base (ZFix f d) = f d

instance (Functor (f d)) => Recursive (ZFix f d) where
    project (ZFix f) = f



-- | Fixed-point for one functor (an 'SFunctor') that takes another functor as
--   a type argument ('ZFunctor'). Not sure but I think
--   @SFix fh f d@ is equivalent to @ZFix (fH f) d@?
newtype SFix (fH :: SFunctor) (f :: ZFunctor) (d :: ILCOrder)
    = SFix (fH f d (SFix fH f d))

type instance ILCDelta (SFix fH f 'HKTValue) = SFix fH f 'HKTDelta

type instance Base (SFix fH f d) = fH f d

instance (Functor (fH f d)) => Recursive (SFix fH f d) where
    project (SFix f) = f


-- | 'ZCofree' is a 'Cofree' where the payload is 'raw' and recursions
--  are Value/Deltas.
--  This is not too useful since we usually want @a@ to also
--  support the value/delta polymorphism, thus 'SCofree' is the
-- type that actually gets used. This is just here for completeness.
data ZCofree (f :: ZFunctor) (d :: ILCOrder) a =
    a :<= (f d (ZCofree f d a))

-- | 'SCofree' is a 'Cofree' where one functor @f@ is applied to
--   the payload @a@
--   and a different functor @fb@ is applied to the recursive/branching part.
data SCofree (fb :: SFunctor) (f :: ZFunctor) (d :: ILCOrder) a =
    (f d a) :<< (fb f d (SCofree fb f d a))

-- | Non fixed-point representation for use with recursion-schemes
data SCofreeF (fb :: SFunctor) (f :: ZFunctor) (d :: ILCOrder) a x =
    (f d a) :<<= (fb f d x)

type instance ILCDelta (SCofree fb f 'HKTValue a) = SCofree fb f 'HKTDelta a

type instance Base (SCofree fb f d a) = SCofreeF fb f d a

instance (Functor (fb f d), Functor (f d)) => Functor (SCofree fb f d) where
    fmap f (a :<< x) = (fmap f a) :<< (fmap (fmap f) x)

instance (Alternative (fb f d), Applicative (f d)) => Applicative (SCofree fb f d) where
    (a :<< x) <*> (b :<< y) = (a <*> b) :<< (liftA2 (<*>) x y)
    pure x = pure x :<< empty

instance (Functor (fb f d), Functor (f d), Comonad (f d)) => Comonad (SCofree fb f d) where
    extract (a :<< _) = extract a
    extend f w@(a :<< as) = undefined


instance (ZJetify f, ZJetify2 (fb f)) => ZJetify (SCofree fb f) where
    toILCDelta (a :<< xa) = a :<< xa
    fromILCDelta (a :<< xa) = a :<< xa
    jetZip :: (SCofree fb f 'HKTValue a, SCofree fb f 'HKTDelta a) -> SCofree fb f 'HKTJet a
    jetZip (a :<< xa, b :<< xb) = undefined --(jetZip (a,b)) :<< (jetZip2 (xa,xb))
    jetUnzip :: SCofree fb f 'HKTJet a -> (SCofree fb f 'HKTValue a, SCofree fb f 'HKTDelta a)
    jetUnzip (z :<< xz) = let (a,b)    = jetUnzip z
                              (xa, xb) = undefined --_fz xz
                          in ( (a :<< xa) , (b :<< xb) )

-- | ZJetify for 'SFunctor's
instance (ZJetify2 (fb f), ZJetify f) => ZJetify2 (SCofree fb f) where
    jetZip2 ( (a :<< xa) , (b :<< xb) ) = undefined --(_f1 (a,b)) :<< (_f2 (xa,xb))
    jetUnzip2 (z :<< xz) = undefined
        
{-
-- | ZJetDist for 'SFunctor'
instance (SJetify (SCofree fb)) => SJetDist (SCofree fb) where
    extractSJet :: (ZJetify f) => SDExpr (s f) 'HKTValue a -> s (SDExpr f) 'HKTValue a
    extractSJet = undefined
    injectSJet :: (ZJetify f) => s (SDExpr f) 'HKTValue a -> SDExpr (s f) 'HKTValue a
    injectSJet = undefined
-}

{-
instance (JetZip (fb f), JetZip f) => JetZip (SCofree fb f) where
    jetZipWith :: ((a,b)-> c) -> (SCofree fb f 'HKTValue a, SCofree fb f 'HKTDelta b) -> SCofree fb f 'HKTJet c
    jetZipWith f ((a :<< x), (da :<< dx)) = (jetZipWith f (a,da)) :<< (jetZipWith (jetZipWith f) (x,dx))
    jetUnzipWith :: (a -> (b,c)) -> SCofree fb f 'HKTJet a -> (SCofree fb f 'HKTValue b, SCofree fb f 'HKTDelta c)
    jetUnzipWith f (ja :<< jx) = let (a,da) = jetUnzipWith f ja
                                     (x,dx) = jetUnzipWith (jetUnzipWith f) jx
                                 in
                                     (a :<< x, da :<< dx)

instance (forall f. (JetZip (SCofree fb f), JetZip (fb f))) => SJetify (SCofree fb) where
    toSJet (a :<< x, da :<< dx) = (toJet (a,da)) :<< (jetZipWith toSJet (x, dx))
    fromSJet (a :<< x) =
        let (a',da') = fromJet a
            (x',dx') = jetUnzipWith fromSJet x
            v  = a'  :<< (x')
            dv = da' :<< (dx')
        in (v,dv)

-}

instance (Functor (fb f d)) => Functor (SCofreeF fb f d a) where
    fmap f (x :<<= xs)  =  x :<<= (fmap f xs)

instance (Functor (fb f d)) => Recursive (SCofree fb f d a) where
    project (a :<< as)  =  a :<<= as

instance PatchInstance (SCofree fb f 'HKTDelta a) where
    (<^<) = undefined
    noPatch = undefined

instance Patchable (SCofree fb f 'HKTValue a) where
    patch = undefined
    changes = undefined


z1 :: Cofree Maybe Integer
z1 = (3 :: Integer) :< Just (4 :< (Just (5 :< Nothing)))

z2 :: Cofree Maybe String
z2 = "argh" :< Just ("ack" :< (Just ("foo" :< Nothing)))

z3 :: EnvT (Cofree Maybe Integer) (Cofree Maybe) String
z3 = EnvT z1 z2

zipZ :: EnvT (Cofree Maybe Integer) (Cofree Maybe) String -> (Integer, String)
zipZ c = let a = extract (ask c)
             x = unwrap (ask c)
             b = extract c
             y = unwrap c
         in (a,b)

