{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

--

-- | A "Scratch Buffer" used for experimental code.
module Blackboard where

--import Data.Monoid (Sum(..))

import Prelude

import Data.Function
import Data.Kind


--import GHC.IO.Encoding (getLocaleEncoding)
import System.IO (hSetEncoding, stderr, stdout, utf8)

import Zorja.Patchable
import Zorja.Primitives
import Zorja.Collections.SplicedList
--import Zorja.Collections.MapValDelta
import Zorja.SumTypeWrapper

import qualified GHC.Generics as GHC
import Generics.SOP


x1 :: ValDelta (ReplaceOnly String)
x1 = ReplaceValDelta "argh" (Replacing (Just "ack"))

x2 :: ValDelta Bool
x2 = BoolChange True False

x3 :: SplicedList (DiffNum Integer)
x3 = SplicedList $ fmap DNum [5,6,1,-3,4]

x5 :: Bool -> DiffNum Integer
x5 True = DNum 3
x5 False = DNum 4

data HKDRoute = HKDValue | HKDDelta | HKDValDelta

type family HKD (f :: HKDRoute) a where
  HKD 'HKDValue a = a
  HKD 'HKDDelta a = ILCDelta a
  HKD 'HKDValDelta a = ValDelta a

--
-- a product type
--

data Thingy f = Thingy {
  _position :: HKD f (ReplaceOnly (Double,Double)),
  _name     :: HKD f (ReplaceOnly String),
  _mesh     :: HKD f (ReplaceOnly String)
  } deriving (GHC.Generic)

--makeLenses ''Thingy

instance (Show (HKD f (ReplaceOnly (Double,Double))),
          Show (HKD f (ReplaceOnly String))
          ) => Show (Thingy f) where
    show (Thingy p n m) = "Thingy (" ++ show p ++ ") (" ++ show n ++ ") (" ++ show m ++ ")"

type instance ILCDelta (Thingy 'HKDValue) = Thingy 'HKDDelta
type instance ValDelta (Thingy 'HKDValue) = Thingy 'HKDValDelta

--instance ValDeltaBundle (Thingy 'HKDValue)
--instance PatchInstance (Thingy 'HKDDelta)
--instance Patchable (Thingy 'HKDValue)


data A a = 
    C a
  | D (DiffNum Integer)
  | E (ReplaceOnly String)
  deriving (Show, GHC.Generic)

$(genDeltaDataTypes ''A)
$(genTypeInstances ''A)
$(genClassInstances ''A)

instance (Show (ILCDelta a)) => Show (A_delta a) where
  show (C_delta dc) = "Cdelta " ++ show dc
  show (D_delta dd) = "Ddelta " ++ show dd
  show (E_delta de) = "Edelta " ++ show de
  
instance (Show (ValDelta a)) => Show (A_valdelta a) where
  show (C_valdelta db) = "Cvaldelta " ++ show db
  show (D_valdelta dd) = "Dvaldelta " ++ show dd
  show (E_valdelta de) = "Evaldelta " ++ show de

x :: A Bool
x = patch (D_valdelta (DValDelta 3 3))

y :: A_valdelta Bool
y = bundleVD ( (C True), (C_delta True))

z :: SumTypeValDelta (A Bool)
z = diffBundle (SumTypeWrapper $ C True) (SumTypeWrapper $ D (DNum 3))


geq :: (Generic a, All2 Eq (Code a)) => a -> a -> Bool
geq = go `on` from
  where
    go :: forall xss. (All2 Eq xss, All SListI xss) => SOP I xss -> SOP I xss -> Bool
    go (SOP (Z xs))  (SOP (Z ys))  = and . hcollapse $ hcliftA2 p eq xs ys
    go (SOP (S xss)) (SOP (S yss)) = go (SOP xss) (SOP yss)
    go _             _             = False

    p :: Proxy Eq
    p = Proxy

    eq :: forall (a :: Data.Kind.Type). Eq a => I a -> I a -> K Bool a
    eq (I a) (I b) = K (a == b)


main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
