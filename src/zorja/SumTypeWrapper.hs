{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.SumTypeWrapper where

-- mostly for bimapping on tuples returned by unbundleVD
import Data.Bifunctor

import Zorja.Patchable

import qualified GHC.Generics as GHC
import Generics.SOP

newtype SumTypeWrapper a = SumTypeWrapper a
  deriving (Eq, Show, GHC.Generic)

data SumTypeDelta a =
    SwitchTagDelta a
  | PatchTagDelta (ILCDelta a)
  deriving (GHC.Generic)

data SumTypeValDelta a =
    OneTag (ValDelta a)
  | ChangeTag a a
  deriving (GHC.Generic)

instance (Show a, Show (ILCDelta a)) => Show (SumTypeDelta a) where
  show (SwitchTagDelta da) = "SwitchTagDelta " ++ show da
  show (PatchTagDelta da) = "PatchTagDelta " ++ show da

instance (Show a, Show (ValDelta a)) => Show (SumTypeValDelta a) where
  show (OneTag aa) = "OneTag " ++ show aa
  show (ChangeTag a a') = "ChangeTag (" ++ show a ++ ") (" ++ show a' ++ ")"

type instance ILCDelta (SumTypeWrapper a) = SumTypeDelta a
type instance ValDelta (SumTypeWrapper a) = SumTypeValDelta a

instance DeltaRelation     (SumTypeWrapper a) (SumTypeDelta a)
instance FlipDeltaRelation (SumTypeDelta a)   (SumTypeWrapper a)
instance ValDeltaRelation     (SumTypeWrapper a)  (SumTypeValDelta a)
instance FlipValDeltaRelation (SumTypeValDelta a)  (SumTypeWrapper a)

instance (ValDeltaBundle a) => ValDeltaBundle (SumTypeWrapper a) where
  bundleVD (SumTypeWrapper a,SwitchTagDelta a') = ChangeTag a a'
  bundleVD (SumTypeWrapper a,PatchTagDelta da) = OneTag (bundleVD (a,da))

  unbundleVD (OneTag aa)      = bimap SumTypeWrapper PatchTagDelta $ unbundleVD aa
  unbundleVD (ChangeTag a a') = (SumTypeWrapper a, SwitchTagDelta a')                           

  valueBundle (SumTypeWrapper a) = OneTag (valueBundle a)

instance (Patchable a, Generic a) => Patchable (SumTypeWrapper a) where
  patch (OneTag aa) = SumTypeWrapper (patch aa)
  patch (ChangeTag _ a') = SumTypeWrapper a'

  diffBundle (SumTypeWrapper a) (SumTypeWrapper a')
    | sameConstructors a a' = OneTag (diffBundle a a')
    | otherwise             = ChangeTag a a'

  changes (SumTypeWrapper a) (SumTypeWrapper a')
    | sameConstructors a a' = PatchTagDelta (changes a a')
    | otherwise             = SwitchTagDelta a'

instance (Patchable a) => PatchInstance (SumTypeDelta a) where
  _                  <^< SwitchTagDelta da'  = SwitchTagDelta da'
  (SwitchTagDelta a) <^< (PatchTagDelta da') = SwitchTagDelta (patch (bundleVD (a,da')))
  (PatchTagDelta da) <^< (PatchTagDelta da') = PatchTagDelta (da <^< da')


-- Returns true if the two values use the same constructor from a given sum type.
-- SOP types represent the different constructos using a Peano encoding
-- of the constructor number, so (Z ...) is the first constructor, (S (Z ...))
-- is the second constructor, and so on. Here we just compare constructors, and
-- if the S/Z counts match the constructors are the same. If the S/Z counts
-- don't match these are two different constructors.
sameConstructors :: (Generic a) => a -> a -> Bool
sameConstructors a b = cs (from a) (from b)
  where
    cs :: SOP I xss -> SOP I xss -> Bool
    cs (SOP (Z _))   (SOP (Z _))   = True
    cs (SOP (S xss)) (SOP (S yss)) = cs (SOP xss) (SOP yss)
    cs _             _             = False



--
-- Take a case statement/pattern match for a sum type and convert into a ValDelta - based function
--
dCase :: (Patchable a, Patchable b) => ((SumTypeWrapper a) -> b) -> (SumTypeValDelta a) -> ValDelta b
dCase fc (OneTag aa)      = let a  = valueUnbundle aa
                                b  = fc (SumTypeWrapper a)
                                b' = fc (SumTypeWrapper (patch aa))
                            in
                                diffBundle b b'
dCase fc (ChangeTag a a') = let b  = fc (SumTypeWrapper a)
                                b' = fc (SumTypeWrapper a')
                            in
                                diffBundle b b'


