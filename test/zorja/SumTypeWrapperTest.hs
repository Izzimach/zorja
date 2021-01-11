{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.SumTypeWrapperTest where

import Data.Text

import Hedgehog
import Hedgehog.Gen as Gen
import Hedgehog.Range

import Zorja.Patchable
import Zorja.PatchableTH
import Zorja.Primitives
import Zorja.SumTypeWrapper

import Zorja.BasicGenerators
import Zorja.PatchableTest
import Zorja.PrimitivesTest

import qualified GHC.Generics as GHC
import Generics.SOP

mkSumTypeGen :: (Patchable a, Generic a) => Gen a -> PatchableGen (SumTypeWrapper a)
mkSumTypeGen g =
  PatchableGen
  {
    value = fmap SumTypeWrapper g,
    delta = \a -> do
                    a' <- fmap SumTypeWrapper g
                    return $ diffBundle a a'
  }

data BasicSumType a =
    ATest a
  | BTest (ReplaceOnly Text)
  | CTest (DiffNum Integer)
  deriving (Show, Eq, GHC.Generic)

$(genDeltaDataTypes ''BasicSumType)
$(genDeltaInstances ''BasicSumType)

instance (Show (ILCDelta a)) => Show (BasicSumType_delta a) where
  show (ATest_delta a) = "ATest_delta " ++ show a
  show (BTest_delta b) = "BTest_delta " ++ show b
  show (CTest_delta c) = "CTest_delta " ++ show c

instance (Show (ValDelta a)) => Show (BasicSumType_valdelta a) where
  show (ATest_valdelta a) = "ATest_valdelta " ++ show a
  show (BTest_valdelta b) = "BTest_valdelta " ++ show b
  show (CTest_valdelta c) = "CTest_valdelta " ++ show c

basicSumTypeValueGen :: Gen a -> Gen (BasicSumType a)
basicSumTypeValueGen g =
  choice
    [
      fmap ATest g,
      fmap BTest (value replaceOnlyTextGen),
      fmap CTest (value diffIntegerGen)
    ]

basicSumTypeGen :: PatchableGen (SumTypeWrapper (BasicSumType Bool))
basicSumTypeGen = mkSumTypeGen (basicSumTypeValueGen Gen.bool)
