{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Hedgehog

import Zorja.PatchableTest
import Zorja.PrimitivesTest
import Zorja.Collections.SplicedListTest
import Zorja.Collections.MapValDeltaTest

--
-- tests of basic patch properties
--

prop_nullpatch :: Property
prop_nullpatch = 
    property $ do
        subprop_nullpatch replaceOnlyIntegerGen
        subprop_nullpatch diffIntegerGen
        subprop_nullpatch replaceOnlyFloatGen
        subprop_nullpatch replaceOnlyTextGen
        subprop_nullpatch splicedIntegerListGen
        subprop_nullpatch replaceOnlyFloatMapGen

-- | patching with (da1 <> da2) should be the same and patching first da1, then da2
prop_patchmerges :: Property
prop_patchmerges = 
    property $ do
        -- start with some simple types
        subprop_patchmerge replaceOnlyIntegerGen
        subprop_patchmerge diffIntegerGen
        subprop_patchmerge replaceOnlyFloatGen
        subprop_patchmerge replaceOnlyTextGen
        subprop_patchmerge splicedIntegerListGen
        subprop_patchmerge replaceOnlyFloatMapGen

-- | patching 'a' with 'changes a b' should produce 'b'
prop_patchchanges :: Property
prop_patchchanges =
    property $ do
        subprop_patchchanges replaceOnlyIntegerGen
        subprop_patchchanges diffIntegerGen
        subprop_patchchanges replaceOnlyFloatGen
        subprop_patchchanges replaceOnlyTextGen
        subprop_patchchanges splicedIntegerListGen
        subprop_patchchanges replaceOnlyFloatMapGen


tests :: IO Bool
tests = checkSequential $$(discover)

main :: IO Bool
main = tests
