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

import Prelude

--import GHC.IO.Encoding (getLocaleEncoding)
import System.IO (hSetEncoding, stderr, stdout, utf8)

import Zorja.Patchable
import Zorja.PatchableTH
import Zorja.Primitives
import Zorja.Collections.SplicedList
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


data A a b = 
    C a
  | D (DiffNum Integer)
  | E b
  deriving (Show, GHC.Generic)

$(genDeltaDataTypes ''A)
$(genDeltaInstances ''A)

instance (Show (ILCDelta a), Show (ILCDelta b)) => Show (A_delta a b) where
  show (C_delta dc) = "Cdelta " ++ show dc
  show (D_delta dd) = "Ddelta " ++ show dd
  show (E_delta de) = "Edelta " ++ show de
  
instance (Show (ValDelta a), Show (ValDelta b)) => Show (A_valdelta a b) where
  show (C_valdelta db) = "Cvaldelta " ++ show db
  show (D_valdelta dd) = "Dvaldelta " ++ show dd
  show (E_valdelta de) = "Evaldelta " ++ show de

x :: A Bool (ReplaceOnly String)
x = patch (D_valdelta (DValDelta 3 3))

y :: A_valdelta Bool (ReplaceOnly Integer)
y = bundleVD ( (C True), (C_delta True))

z :: SumTypeValDelta (A Bool (ReplaceOnly String))
z = diffBundle (SumTypeWrapper $ C True) (SumTypeWrapper $ E (ReplaceOnly "Argh"))


main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
