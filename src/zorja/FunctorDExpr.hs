{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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

import Data.Distributive
import Data.Kind (Type)
import Data.Proxy

import Fcf.Core

import Zorja.Patchable
import Zorja.ZHOAS
    

--
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
    rfdmap :: Proxy d -> (a -> b) -> (Eval (ReifyFunctorD d a)) -> (Eval (ReifyFunctorD d b))



-- The purpose of @RFType@ and @RFTypeD@ are to carry around
-- the functor as a packaged-up type so that it can be used in computing
-- related/derived data types.
-- the underlaying data value is of the form (Eval (ReifyFunctor d a))

-- | A newtype wrapper around `Eval (ReifyFunctor d a))'
newtype RFType d a = RFT { unRFT :: (Eval (ReifyFunctor d a)) }

-- | A newtype wrapper around 'Eval (ReifyFunctorD d a))'
newtype RFTypeD d a = RFTD { unRFTD :: (Eval (ReifyFunctorD d a)) }

instance (Show (Eval (ReifyFunctor d a))) => Show (RFType d a) where
    show (RFT x) = "ReifiedFunctor: " ++ show x
instance (Show (Eval (ReifyFunctorD d a))) => Show (RFTypeD d a) where
    show (RFTD x) = "ReifiedFunctorD: " ++ show x
    
type instance ILCDelta (RFType d a) = RFTypeD d a

instance (ReifyFmap d) => Functor (RFType d) where
    fmap f (RFT a) = RFT $ rfmap (Proxy @d) f a

instance (ReifyFmap d) => Functor (RFTypeD d) where
    fmap f (RFTD a) = RFTD $ rfdmap (Proxy @d) f a





-- |'ZFExpr' is a 'ZDExpr' where both 'a' and 'da' can be expressed as
-- functors.


-- | 'ZFExpr', a 'ZDExpr' where both the value @x@ and the delta @dx@ are
--  functors of @a@, for example:
--  - @x :: f1 a@
--  - @dx :: f2 a@
-- where @f1@ and @f2@ are both functors. This allows 'ZFExpr' to be a 'Functor'
-- so it can be used in (for example) catamorphisms.
-- To use this your base type @a@ has to be an 'RFType' so the typechecker
-- can correctly figure out the 'ILCDelta' of computed and 'fmap' related types.

data ZFExpr d a = ZFE (RFType d a) (RFTypeD d a)

toZFExpr :: ZDExpr (RFType d a) -> ZFExpr d a
toZFExpr (ZDV a da) = ZFE a da

fromZFExpr :: (Patchable (RFType d a)) => ZFExpr d a -> ZDExpr (RFType d a)
fromZFExpr (ZFE fa fda) = ZDV fa fda

instance (Show (RFType d a), Show (RFTypeD d a)) => Show (ZFExpr d a) where
    show (ZFE a da) = "ZFExpr: " ++ show a ++ " / " ++ show da

instance (ReifyFmap d) => Functor (ZFExpr d) where
    fmap f (ZFE (RFT x) (RFTD xd)) = ZFE (RFT $ rfmap (Proxy @d) f x) (RFTD $ rfdmap (Proxy @d) f xd)


instance (ReifyFmap d, Distributive (RFType d), Distributive (RFTypeD d)) 
    => Distributive (ZFExpr d) where
    distribute xs = ZFE (collect getA xs) (collect getDA xs)
        where
            getA (ZFE a _) = a
            getDA (ZFE _ b) = b

instance (Foldable (RFType d), Foldable (RFTypeD d))
    => Foldable (ZFExpr d) where
    foldMap f (ZFE a da) = (foldMap f a) <> (foldMap f da)

instance (ReifyFmap d, Traversable (RFType d), Traversable (RFTypeD d))
    => Traversable (ZFExpr d) where
    traverse f (ZFE fa dfa) = ZFE <$> (traverse f fa) <*> (traverse f dfa)



-- | NoWrap is basically "no-functor". Note that to use this with FDExpr's,
-- the inner type has to be its own delta.
data NoWrap :: DeferredFunctor k

type instance Eval (ReifyFunctor  NoWrap a) = a
type instance Eval (ReifyFunctorD NoWrap a) = a

instance ReifyFmap NoWrap where
    rfmap _ f a = f a
    rfdmap _ f da = f da

