{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Data.Semigroup
import qualified Data.Text as T

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Zorja.Primitives


import Subtests.PatchGen
import Subtests.Primitives
import Subtests.ListX
--import Subtests.ZJIntMap
import Subtests.Cofree

-- some basic generators

basic_intgen :: Gen Integer
basic_intgen = Gen.integral $ Range.linear (0::Integer) (10000::Integer)

basic_floatgen :: Gen Float
basic_floatgen = Gen.float $ Range.linearFrac (0.0::Float) (10000.0::Float)

basic_textgen :: Gen T.Text
basic_textgen = Gen.text (Range.linear 0 20) Gen.unicode

basic_replaceOnlyint = gen_ReplaceOnly basic_intgen
basic_replaceOnlyfloat = gen_ReplaceOnly basic_floatgen
basic_replaceOnlytext = gen_ReplaceOnly basic_textgen

basic_ListXfloat = fromFDEGen . gen_ListX . toFDEGen $ basic_replaceOnlyfloat
basic_ZJItemMapint = fromFDEGen . gen_ZJItemMap . toFDEGen $ basic_replaceOnlyfloat

basic_replaceOnlySumInt :: PatchableGen (ReplaceOnly (Sum Integer))
basic_replaceOnlySumInt = gen_ReplaceOnly (fmap (Sum) basic_intgen)

patchgen_CofTreeint = fromFDEGen $ 
    gen_CofDTree 
        (toFDEGen basic_replaceOnlySumInt)
        (gen_ZJItemMap . gen_ReplaceOnlyFDE)

--
-- tests of basic patch properties
--

-- | patching with (da1 <> da2) should be the same and patching first da1, then da2
prop_patchmerge :: Property
prop_patchmerge = 
    property $ do
        -- start with some simple types
        subprop_patchmerge basic_replaceOnlyint
        subprop_patchmerge basic_replaceOnlyfloat
        subprop_patchmerge basic_replaceOnlytext
        -- ListX
        subprop_patchmerge basic_ListXfloat
        subprop_patchmerge basic_ZJItemMapint
        subprop_patchmerge patchgen_CofTreeint

-- | patching 'a' with 'changes a b' should produce 'b'
prop_patchchanges :: Property
prop_patchchanges =
    property $ do
        subprop_patchchanges basic_replaceOnlytext
        subprop_patchchanges basic_ZJItemMapint
        -- can't test ListX since it doesn't work on different-sized lists
        --subprop_patchchanges (fromFDEGen $ gen_ListX $ toFDEGen $ gen_ReplaceOnly floatgen)
        subprop_patchchanges patchgen_CofTreeint




tests :: IO Bool
tests = checkSequential $$(discover)

main :: IO Bool
main = tests
