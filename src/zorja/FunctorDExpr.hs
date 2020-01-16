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


-- | A ZFunctor that's just the value itself with no wrapper.
type ZNoWrap (d :: ILCOrder) a = a

-- | A way to combine/break apart value/delta pairs
class ZJetify (f :: ZFunctor) where
    fromJet :: f 'HKTJet a -> (f 'HKTValue a, f 'HKTDelta a)
    toJet   :: (f 'HKTValue a, f 'HKTDelta a) -> f 'HKTJet a

-- | Jetify for 'SFunctor's
class SJetify (s :: SFunctor) where
    fromSJet :: (ZJetify f) => s f 'HKTJet a -> (s f 'HKTValue a, s f 'HKTDelta a)
    toSJet   :: (ZJetify f) => (s f 'HKTValue a, s f 'HKTDelta a) -> s f 'HKTJet a

-- | Version of zipWith where two operands are 'HKTValue' and 'HKTDelta' types, that
--   get  into 'HKTJet'.
class SJetZip (f :: ZFunctor) where
    jetZipWith :: (a -> b -> c) -> f 'HKTValue a -> f 'HKTDelta b -> f 'HKTJet c
    jetUnzipWith :: (a -> (b,c)) -> f 'HKTJet a -> (f 'HKTValue b, f 'HKTDelta c)

--

-- | Identity as a `ZFunctor`
data family ZIdentity (d :: ILCOrder) a

data instance ZIdentity 'HKTValue a = ZIdentity a
    deriving (Eq, Show)
data instance ZIdentity 'HKTDelta a = ZDIdentity a
    deriving (Eq, Show)
data instance ZIdentity 'HKTJet a = ZJet a a
    deriving (Eq, Show)

type instance ILCDelta (ZIdentity 'HKTValue a) = ZIdentity 'HKTDelta a

instance ZJetify ZIdentity where
    fromJet (ZJet a da) = (ZIdentity a, ZDIdentity da)
    toJet (ZIdentity a, ZDIdentity da) = ZJet a da

instance Functor (ZIdentity 'HKTValue) where
    fmap f (ZIdentity a) = ZIdentity (f a)

instance Functor (ZIdentity 'HKTDelta) where
    fmap f (ZDIdentity a) = ZDIdentity (f a)

instance Functor (ZIdentity 'HKTJet) where
    fmap f (ZJet a b) = ZJet (f a) (f b)




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

instance (ZJetify f) => ZJetify (ZList f) where
    fromJet (ZList aj) = let (a, da) = unzip $ fmap fromJet aj
                         in (ZList a, ZList da)
    toJet (ZList a, ZList da) = ZList $ zipWith (curry toJet) a da

instance SJetify ZList where
    fromSJet (ZList x) = let (x', dx') = unzip $ fmap fromJet x
                         in (ZList x', ZList dx')
    toSJet (ZList x, ZList dx) = ZList $ zipWith (curry toJet) x dx

data ZMaybe (f :: ZFunctor) (d :: ILCOrder) a =
      ZJust (f d a)
    | ZNothing
    deriving (Eq, Show)

type instance ILCDelta (ZMaybe f 'HKTValue a) = ZMaybe f 'HKTDelta a

instance (Functor (f d)) => Functor (ZMaybe f d) where
    fmap f (ZJust a) = ZJust (fmap f a)
    fmap _ ZNothing = ZNothing

instance (ZJetify f) => ZJetify (ZMaybe f) where
    fromJet ZNothing = (ZNothing, ZNothing)
    fromJet (ZJust x) = let (a,da) = fromJet x
                        in (ZJust a, ZJust da)
    toJet (ZNothing, ZNothing) = ZNothing
    toJet (ZJust a,  ZJust da) = ZJust (toJet (a,da))
    toJet (_,        _)        = ZNothing




-- | Fix point (recursive) data structure for' ZFunctor' types.
newtype ZFix (f :: ZFunctor) (d :: ILCOrder) 
    = ZFix (f d (ZFix f d))

type instance ILCDelta (ZFix f 'HKTValue) = ZFix f 'HKTDelta

type instance Base (ZFix f d) = f d

instance (Functor (f d)) => Recursive (ZFix f d) where
    project (ZFix f) = f



-- | Fixed-point for one functor (an SFunctor) that takes another functor as
--   a type argument (ZFunctor). Not sure but I think
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
--  support the value/delta polymorphism, thus 'SCofree'.
data ZCofree (f :: ZFunctor) (d :: ILCOrder) a =
    a :<= (f d (ZCofree f d a))

-- | 'SCofree' is a 'Cofree' where one functor @f@ is applied to
--   the payload @a@
--   and a different functor @fb@ is applied to the recursive part.
data SCofree (fb :: SFunctor) (f :: ZFunctor) (d :: ILCOrder) a =
    (f d a) :<< (fb f d (SCofree fb f d a))

-- | Non fixed-point representation for recursion-schemes
data SCofreeF (fb :: SFunctor) (f :: ZFunctor) (d :: ILCOrder) a x =
    (f d a) :<<= (fb f d x)

type instance ILCDelta (SCofree fb f 'HKTValue a) = SCofree fb f 'HKTDelta a

type instance Base (SCofree fb f d a) = SCofreeF fb f d a

instance (Functor (fb f d), Functor (f d)) => Functor (SCofree fb f d) where
    fmap f (a :<< x) = (fmap f a) :<< (fmap (fmap f) x)

instance (Alternative (fb f d), Applicative (f d)) => Applicative (SCofree fb f d) where
    (a :<< x) <*> (b :<< y) = (a <*> b) :<< (liftA2 (<*>) x y)
    pure x = pure x :<< empty

instance (SJetZip (fb f), SJetZip f) => SJetZip (SCofree fb f) where
    jetZipWith :: (a -> b -> c) -> SCofree fb f 'HKTValue a -> SCofree fb f 'HKTDelta b -> SCofree fb f 'HKTJet c
    jetZipWith f (a :<< x) (da :<< dx) = (jetZipWith f a da) :<< (jetZipWith (jetZipWith f) x dx)
    jetUnzipWith :: (a -> (b,c)) -> SCofree fb f 'HKTJet a -> (SCofree fb f 'HKTValue b, SCofree fb f 'HKTDelta c)
    jetUnzipWith f (ja :<< jx) = let (a,da) = jetUnzipWith f ja
                                     (x,dx) = jetUnzipWith (jetUnzipWith f) jx
                                 in
                                     (a :<< x, da :<< dx)

instance (Functor (fb f d)) => Functor (SCofreeF fb f d a) where
    fmap f (x :<<= xs)  =  x :<<= (fmap f xs)

instance (Functor (fb f d)) => Recursive (SCofree fb f d a) where
    project (a :<< as)  =  a :<<= as

instance (forall f. (SJetZip (SCofree fb f),  SJetZip (fb f))) => SJetify (SCofree fb) where
    toSJet (a :<< x, da :<< dx) = (toJet (a,da)) :<< (jetZipWith (\x y-> toSJet (x,y)) x dx)
    fromSJet (a :<< x) =
        let (a',da') = fromJet a
            (x',dx') = jetUnzipWith fromSJet x
            v  = a'  :<< (x')
            dv = da' :<< (dx')
        in (v,dv)

data ZZFExpr (f :: ZFunctor) a = ZZFE (f 'HKTValue a) (f 'HKTDelta a)

instance (Show (f 'HKTValue a), Show (f 'HKTDelta a)) => Show (ZZFExpr f a) where
    show (ZZFE f df) = "ZFExpr (" ++ show f ++ "/\\/" ++ show df ++ ")"

instance (Eq (f 'HKTValue a), Eq (f 'HKTDelta a)) => Eq (ZZFExpr f a) where
    (ZZFE a da) == (ZZFE b db) = (a == b) && (da == db)

instance (Functor (f 'HKTValue), Functor (f 'HKTDelta)) => Functor (ZZFExpr f) where
    fmap f (ZZFE a da) = ZZFE (fmap f a) (fmap f da)


-- * Deferred Functors
--
-- $deferredFunctors
--
-- When working with 'ILCDelta' values the typechecker needs to automatically
-- derive deltas of possibly complicated and recursive functors. To
-- avoid madness in figuring out types here I take the complete type @d a@ and
-- separate it into the deferred functor @d@ applied to a payload @a@.
--
-- Given some kind @d@ and payload type @a@ the final type is
--  @Eval (x d a)@ where @x@ is either 'ReifyFunctor' or 'ReifyFunctorD' depending
-- on whether you want a functor or it's delta.
--
-- To use this, define an empty data type
--
-- > data X :: DeferredFunctor k)
--
-- and associated functors @FX@ and @FXD@ which are the functor and it's delta.
-- that are associated with @X@. Then write two type instances to 'compute'
-- @FX@ and @FXD@ from @X@:
--
-- > type instance Eval (ReifyFunctor  X a) = FX a
-- > type instance Eval (ReifyFunctorD X a) = FXD a
--
-- Look at 'NoWrap' or 'ListX' as an example.

-- | This is equivalent to 'Fcf.Exp'. The 'DeferredFunctor' is a datakind which
-- describes a 'Functor' @d@ that has not yet been applied to its "payload" @a@.
-- The application of the functor to its payload happens when 'Eval'-ing
-- via 'ReifyFunctor' or 'ReifyFunctorD'. In this case a single datakind is used
-- to derive both a functor (using 'ReifyFunctor') and that functors 'ILCDelta'
-- (using 'ReifyFunctorD')
type DeferredFunctor k = k -> Type

-- | Given some 'DeferredFunctor' and a target payload, 'Eval'-ing this will
-- produce the type @(f1 a)@ where the Functor @f1@ is associated with the 
-- datakind @d@
data ReifyFunctor  (d :: DeferredFunctor k) a :: Exp Type

-- | Given some 'DeferredFunctor' and a target payload, 'Eval'-ing this will
-- produce the type @(f2 a)@  where the Functor @f2@ is associated with the
-- datakind @d@ and @(f2 a)@ is the 'ILCDelta' of @(f1 a)@
data ReifyFunctorD (d :: DeferredFunctor k) a :: Exp Type

-- | This typeclass 'ReifyFmap' indicates that for a given 'DeferredFunctor' @d@, there
-- exist related 'Functor' instances derived using 'ReifyFunctor' and 'ReifyFunctorD'
-- version, which allows us to 'fmap' a function @f@ over both a value and its 'ILCDelta'
class ReifyFmap (d :: DeferredFunctor k) where
    rfmap :: Proxy d -> (a -> b) -> (Eval (ReifyFunctor d a)) -> (Eval (ReifyFunctor d b))
    rfmapD :: Proxy d -> (a -> b) -> (Eval (ReifyFunctorD d a)) -> (Eval (ReifyFunctorD d b))

class (ReifyFmap d) => ReifyFapplicative (d :: DeferredFunctor k) where
    rfpure :: Proxy d -> a -> Eval (ReifyFunctor d a)
    rfliftA2 :: Proxy d -> (a -> b -> c)
                        -> Eval (ReifyFunctor d a) 
                        -> Eval (ReifyFunctor d b)
                        -> Eval (ReifyFunctor d c)
    rfpureD :: Proxy d -> a -> Eval (ReifyFunctorD d a)
    rfliftA2D :: Proxy d -> (a -> b -> c)
                         -> Eval (ReifyFunctorD d a) 
                         -> Eval (ReifyFunctorD d b)
                         -> Eval (ReifyFunctorD d c)

class ReifyFfoldable (d :: DeferredFunctor k) where
    rffoldMap :: (Monoid m) => Proxy d
                               -> (a -> m)
                               -> Eval (ReifyFunctor d a) -> m
    rffoldMapD :: (Monoid m) => Proxy d
                                -> (a -> m)
                                -> Eval (ReifyFunctorD d a) -> m

class (ReifyFfoldable d) => ReifyFtraversable (d :: DeferredFunctor k) where
    rftraverse :: (Applicative f) => Proxy d
                                     -> (a -> f b)
                                     -> Eval (ReifyFunctor d a)
                                     -> f (Eval (ReifyFunctor d b))
    rftraverseD :: (Applicative f) => Proxy d
                                     -> (a -> f b)
                                     -> Eval (ReifyFunctorD d a)
                                     -> f (Eval (ReifyFunctorD d b))
                   

class (ReifyFmap d) => ReifyFdistributive (d :: DeferredFunctor k) where
    rfdistribute :: (Functor f) => Proxy d -> Proxy a 
                                   -> f (Eval (ReifyFunctor d a))
                                   -> Eval (ReifyFunctor d (f a))
    rfdistributeD :: (Functor f) => Proxy d -> Proxy a 
                                    -> f (Eval (ReifyFunctorD d a))
                                    -> Eval (ReifyFunctorD d (f a))

-- | 'Base' working at the kind level. If
-- 
--   > y = Eval (ReifyFunctor f a)
--
--   then
--
--   > Base y x = Eval (ReifyFunctor (RFBase f a) x)
--
type family RFBase (d :: DeferredFunctor k) a :: DeferredFunctor k

class ReifyFrecursive (d :: DeferredFunctor k) where
    rfproject :: Proxy d -> Proxy a 
                 -> Eval (ReifyFunctor d a) 
                 -> Eval (ReifyFunctor (RFBase d a) (Eval (ReifyFunctor d a)))
    rfprojectD :: Proxy d -> Proxy a 
                 -> Eval (ReifyFunctorD d a) 
                 -> Eval (ReifyFunctorD (RFBase d a) (Eval (ReifyFunctorD d a)))

class ReifyFcorecursive (d :: DeferredFunctor k) where
    rfembed :: Proxy d -> Proxy a 
               -> Eval (ReifyFunctor (RFBase d a) (Eval (ReifyFunctor d a)))
               -> Eval (ReifyFunctor d a) 
    rfembedD :: Proxy d -> Proxy a 
               -> Eval (ReifyFunctorD (RFBase d a) (Eval (ReifyFunctorD d a)))
               -> Eval (ReifyFunctorD d a) 
                
-- $rfTypeWrapper
--
-- The purpose of @RFType@ and @RFTypeD@ are to carry around
-- the functor as a packaged-up type so that it can be used in computing
-- related/derived data types.
-- the underlaying data value is of the form (Eval (ReifyFunctor d a))

-- | A newtype wrapper around `Eval (ReifyFunctor d a))'
newtype RFType d a = RFT { unRFT :: (Eval (ReifyFunctor d a)) }

-- | A newtype wrapper around 'Eval (ReifyFunctorD d a))'
newtype RFTypeD d a = RFTD { unRFTD :: (Eval (ReifyFunctorD d a)) }

twoProxyRF :: RFTypeD d a -> (Proxy d, Proxy a)
twoProxyRF _v = (Proxy, Proxy)

instance (Show (Eval (ReifyFunctor d a))) => Show (RFType d a) where
    show (RFT x) = "ReifiedFunctor: " ++ show x
instance (Show (Eval (ReifyFunctorD d a))) => Show (RFTypeD d a) where
    show (RFTD x) = "ReifiedFunctorD: " ++ show x
    
type instance ILCDelta (RFType d a) = RFTypeD d a

instance (ReifyFmap d) => Functor (RFType d) where
    fmap f (RFT a) = RFT $ rfmap (Proxy @d) f a

instance (ReifyFmap d) => Functor (RFTypeD d) where
    fmap f (RFTD a) = RFTD $ rfmapD (Proxy @d) f a

instance (ReifyFapplicative d) => Applicative (RFType d) where
    pure a = RFT $ rfpure (Proxy @d) a
    liftA2 f (RFT a) (RFT b) = RFT $ rfliftA2 (Proxy @d) f a b

instance (ReifyFapplicative d) => Applicative (RFTypeD d) where
    pure a = RFTD $ rfpureD (Proxy @d) a
    liftA2 f (RFTD a) (RFTD b) = RFTD $ rfliftA2D (Proxy @d) f a b

instance (ReifyFfoldable d) => Foldable (RFType d) where
    foldMap f (RFT a) = rffoldMap (Proxy @d) f a

instance (ReifyFfoldable d) => Foldable (RFTypeD d) where
    foldMap f (RFTD a) = rffoldMapD (Proxy @d) f a

instance (ReifyFmap d, ReifyFtraversable d) => Traversable (RFType d) where
    traverse f (RFT a) = fmap RFT $ rftraverse (Proxy @d) f a

instance (ReifyFmap d, ReifyFtraversable d) => Traversable (RFTypeD d) where
    traverse f (RFTD a) = fmap RFTD $ rftraverseD (Proxy @d) f a
                        
instance (ReifyFdistributive d) => Distributive (RFType d) where
    distribute x = dist x
        where
            -- need to use a where clause so we can pull out the types and populate proxies
            dist :: forall a f dx. (Functor f, ReifyFdistributive dx) => f (RFType dx a)  -> RFType dx (f a)
            dist fga = RFT $ rfdistribute (Proxy @dx) (Proxy @a) (fmap unRFT fga)

instance (ReifyFdistributive d) => Distributive (RFTypeD d) where
    distribute x = dist x
        where
            -- need to use a where clause so we can pull out the types and populate proxies
            dist :: forall a f dx. (Functor f, ReifyFdistributive dx) => f (RFTypeD dx a)  -> RFTypeD dx (f a)
            dist fga = RFTD $ rfdistributeD (Proxy @dx) (Proxy @a) (fmap unRFTD fga)

--type instance RFBase (RFType d) a = RFBase d a
type instance Base (RFType  d a) = RFType (RFBase  d a)
type instance Base (RFTypeD d a) = RFTypeD (RFBase d a)

instance (ReifyFmap (RFBase d a), ReifyFrecursive d) => Recursive (RFType d a) where
    project (RFT x) = RFT $ rfmap (Proxy @(RFBase d a)) t $ rfproject (Proxy @d) (Proxy @a) x
      where
          -- ugh, type mangling
          t :: Eval (ReifyFunctor d a) -> RFType d a
          t y = RFT y

instance (ReifyFmap (RFBase d a), ReifyFrecursive d) => Recursive (RFTypeD d a) where
    project (RFTD x) = RFTD $ rfmapD (Proxy @(RFBase d a)) t $ rfprojectD (Proxy @d) (Proxy @a) x
        where
            -- ugh, type mangling
            t :: Eval (ReifyFunctorD d a) -> RFTypeD d a
            t y = RFTD y

instance (ReifyFmap (RFBase d a), ReifyFcorecursive d) => Corecursive (RFType d a) where
    embed (RFT x) = RFT $ rfembed (Proxy @d) (Proxy @a) $ rfmap (Proxy @(RFBase d a)) t x
        where
            t :: RFType d a -> Eval (ReifyFunctor d a)
            t = unRFT

instance (ReifyFmap (RFBase d a), ReifyFcorecursive d) => Corecursive (RFTypeD d a) where
    embed (RFTD x) = RFTD $ rfembedD (Proxy @d) (Proxy @a) $ rfmapD (Proxy @(RFBase d a)) t x
        where
            t :: RFTypeD d a -> Eval (ReifyFunctorD d a)
            t = unRFTD
                                                
-- $zfExpressions
--                         
-- 'ZFExpr' is a 'ZDExpr' where both the value @x@ and the delta @dx@ are
--  functors of @a@, for example:
--  - @x :: f1 a@
--  - @dx :: f2 a@
-- where @f1@ and @f2@ are both functors. This allows 'ZFExpr' to be a 'Functor'
-- so it can be used in (for example) catamorphisms.
-- To use this your base type @a@ has to be an 'RFType' so the typechecker
-- can correctly figure out the 'ILCDelta' of computed and 'fmap' related types.
--

data ZFExprK (d :: DeferredFunctor k) :: DeferredFunctor k

type instance Eval (ReifyFunctor (ZFExprK d) a) = ZFExpr d a

-- | Holds a datatype @d a@ and its 'ILCDelta'. The use of
-- 'RFType' is to keep @d@ available for later use.
data ZFExpr d a = ZFE (RFType d a) (RFTypeD d a)

toZFExpr :: ZDExpr (RFType d a) -> ZFExpr d a
toZFExpr (ZDV a da) = ZFE a da

fromZFExpr :: (Patchable (RFType d a)) => ZFExpr d a -> ZDExpr (RFType d a)
fromZFExpr (ZFE fa fda) = ZDV fa fda

instance (Show (RFType d a), Show (RFTypeD d a)) => Show (ZFExpr d a) where
    show (ZFE a da) = "ZFExpr: " ++ show a ++ " / " ++ show da

instance (ReifyFmap d) => Functor (ZFExpr d) where
    fmap f (ZFE a da) = ZFE (fmap f a) (fmap f da)

-- | The 'Applicative' machinery is forwarded via 'RFType' similar to
--  the 'Functor' instance for 'ZFExpr'
instance (ReifyFapplicative d) => Applicative (ZFExpr d) where
    pure a = ZFE (pure a) (pure a)
    liftA2 f (ZFE a da) (ZFE b db) = ZFE (liftA2 f a b) (liftA2 f da db)

-- There is no Foldable or Traversable instance for 'ZFExpr' here
-- since it doesn't seem to make sense. To fold a @ZFE a da@ we would need
-- to combine @a@ and @da@ which is never what you want. Really you want to
-- fold up @a@ and @da@ separately into @ma@ and @mda@ and build a new
-- @ZFE ma mda@ with the result. This would be something more like
-- @traverse . (foldMap f) . distribute@

instance (ReifyFmap d, Distributive (RFType d), Distributive (RFTypeD d)) 
    => Distributive (ZFExpr d) where
    distribute xs = ZFE (collect getA xs) (collect getDA xs)
        where
            getA (ZFE a _) = a
            getDA (ZFE _ b) = b

-- don't think this is what I want, but is left here for reference
{-
instance (Foldable (RFType d), Foldable (RFTypeD d))
    => Foldable (ZFExpr d) where
    foldMap f (ZFE a da) = (foldMap f a) <> (foldMap f da)

instance (ReifyFmap d, Traversable (RFType d), Traversable (RFTypeD d))
    => Traversable (ZFExpr d) where
    traverse f (ZFE fa dfa) = ZFE <$> (traverse f fa) <*> (traverse f dfa)
-}


-- | NoWrap is basically "no-functor". Note that to use this with FDExpr's,
-- the inner type has to be its own delta.
data NoWrap :: DeferredFunctor k

type instance Eval (ReifyFunctor  NoWrap a) = a
type instance Eval (ReifyFunctorD NoWrap a) = a

instance ReifyFmap NoWrap where
    rfmap _ f a = f a
    rfmapD _ f da = f da

