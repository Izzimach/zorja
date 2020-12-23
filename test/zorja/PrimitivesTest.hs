{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Zorja.PrimitivesTest where

-- for Sum type
import Data.Semigroup

import qualified Data.Text as T

import Hedgehog
import qualified Hedgehog.Gen as Gen

import Zorja.Primitives
import Zorja.BasicGenerators
import Zorja.PatchableTest



--
-- | Generator for the ReplaceOnly primitive.  Given a value generator
--  this will produce something to generate values and deltas.
--
mkReplaceOnlyGen :: Gen a -> PatchableGen (ReplaceOnly a)
mkReplaceOnlyGen g =
    PatchableGen
    {
        value = fmap ReplaceOnly g,
        delta = \(ReplaceOnly a) -> Gen.frequency
            [
                (1, (Gen.constant $ ReplaceValDelta a (Replacing Nothing))),
                (3, fmap (\x -> ReplaceValDelta a (Replacing $ Just x)) g)
            ]
    }

-- | Generator for DiffNu primitive
mkDiffNumGen :: Gen a -> PatchableGen (DiffNum a)
mkDiffNumGen g =
    PatchableGen
    {
        value = fmap DNum g,
        delta = \(DNum a) -> fmap (\x -> DValDelta a x) g
    }

replaceOnlyIntegerGen :: PatchableGen (ReplaceOnly Integer)
replaceOnlyIntegerGen = mkReplaceOnlyGen basic_integergen

diffIntegerGen :: PatchableGen (DiffNum Integer)
diffIntegerGen = mkDiffNumGen basic_integergen

replaceOnlyFloatGen :: PatchableGen (ReplaceOnly Float)
replaceOnlyFloatGen = mkReplaceOnlyGen basic_floatgen

replaceOnlyTextGen :: PatchableGen (ReplaceOnly T.Text)
replaceOnlyTextGen = mkReplaceOnlyGen basic_textgen

replaceOnlySumIntGen :: PatchableGen (ReplaceOnly (Sum Integer))
replaceOnlySumIntGen = mkReplaceOnlyGen (fmap (Sum) basic_integergen)

