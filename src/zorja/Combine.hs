{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}



module Zorja.Combine where

import Data.Kind
import Data.Functor.Identity
import Data.Functor.Foldable

import Control.Applicative
import Control.Comonad.Cofree
import qualified Control.Comonad.Trans.Cofree as CCTC


-- | A generic way to combine two values. Normally this would (a,b) but sometimes we want to
--  glom together two things into a different type.
class T2Combine wa vb where
    type T2Combined wa vb :: Type
    t2Combine :: (wa, vb) -> T2Combined wa vb
    t2Sunder :: T2Combined wa vb -> (wa, vb)

--
-- | 'T2Combine' for higher order types. A pseudo-zip for two different types @w@ and @v@
--
class T2Zip w v where
    type T2Zipped w v :: Type -> Type
    t2Zip :: (w a, v a) -> T2Zipped w v a
    t2Unzip :: T2Zipped w v a -> (w a, v a)

-- | 'T2Combine' combines elemental types, and zip combines two functor-like data types
--   that have the same argument type, for example @(w a, v a)@.  Sometimes we want the wrapped
--   type @a@ to be different and combinable, basically @(w a, v b)@. In this case @a@ and @b@
--   must be combinable: @T2Combine a b@
class T2ZipCombine w v where
    type T2ZipCombined w v :: Type -> Type
    t2ZipCombine :: (T2Combine a b) => (w a, v b) -> T2ZipCombined w v (T2Combined a b)
    t2UnzipSunder :: (T2Combine a b) => T2ZipCombined w v (T2Combined a b) -> (w a, v b)



--
-- instances of T2Zip and T2ZipCombine for Identity
--

instance (T2Combine a b) => T2Combine (Identity a) (Identity b) where
    type T2Combined (Identity a) (Identity b) = Identity (T2Combined a b)
    t2Combine (Identity a, Identity b) = Identity (t2Combine (a,b))
    t2Sunder (Identity x) = let (a,b) = t2Sunder x
                            in (Identity a, Identity b)
    
{- let's not use TwoVal at the moment

nstance T2Zip Identity Identity where
    type T2Zipped Identity Identity = TwoVal Identity Identity
    t2Zip (ia0, ia1) = TwoVal ChooseOne ia0 ia1
    t2Unzip (TwoVal _ ia0 ia1) = (ia0,ia1)
-}

instance T2ZipCombine Identity Identity where
    type T2ZipCombined Identity Identity = Identity
    t2ZipCombine (Identity a, Identity b) = Identity (t2Combine (a, b))
    t2UnzipSunder (Identity x) = let (a,b) = t2Sunder x
                                 in (Identity a, Identity b)

instance (T2Combine a b) => T2ZipCombine (Const a) (Const b) where
    type T2ZipCombined (Const a) (Const b) = Const (T2Combined a b)
    t2ZipCombine (Const a0, Const a1) = Const (t2Combine (a0,a1))
    t2UnzipSunder (Const x) = let (a,b) = t2Sunder x
                              in (Const a, Const b)

type instance Base (Identity a) = Const (Identity a)
instance Recursive (Identity a) where project = Const
instance Corecursive (Identity a) where embed = getConst


--
-- T2 Combine and Zip for Cofree/CofreeF

instance (T2ZipCombine f1 f2, T2Combine a1 a2) => T2Combine (Cofree f1 a1) (Cofree f2 a2)  where
    type T2Combined (Cofree f1 a1) (Cofree f2 a2) = Cofree (T2ZipCombined f1 f2) (T2Combined a1 a2)
    t2Combine (a0 :< xs0, a1 :< xs1) = (t2Combine (a0, a1) ) :< (t2ZipCombine (xs0,xs1))
    t2Sunder (a :< xs) = let (a0,a1) = t2Sunder a
                             (xs0, xs1) = t2UnzipSunder xs
                         in
                             (a0 :< xs0, a1 :< xs1)

instance (T2ZipCombine f1 f2, T2Combine a1 a2) => T2ZipCombine (CCTC.CofreeF f1 a1) (CCTC.CofreeF f2 a2) where
    type T2ZipCombined (CCTC.CofreeF f1 a1) (CCTC.CofreeF f2 a2) = CCTC.CofreeF (T2ZipCombined f1 f2) (T2Combined a1 a2)
    t2ZipCombine (a0 CCTC.:< xs0, a1 CCTC.:< xs1) = (t2Combine (a0,a1)) CCTC.:< (t2ZipCombine (xs0,xs1))
    t2UnzipSunder (a CCTC.:< xs) = let (a0,a1) = t2Sunder a
                                       (xs0, xs1) = t2UnzipSunder xs
                                   in
                                       (a0 CCTC.:< xs0, a1 CCTC.:< xs1)



