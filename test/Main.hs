{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


import Subtests.PatchGen
import Subtests.Primitives
import Subtests.ListX

prop_patchmerge :: Property
prop_patchmerge = 
    property $ do
        let intgen   = Gen.integral $ Range.linear (-1000::Integer) (10000::Integer)
        let floatgen = Gen.float $ Range.linearFrac (-1000.0::Float) (10000.0::Float)
        subprop_patchmerge (gen_ReplaceOnly intgen)
        subprop_patchmerge (gen_ReplaceOnly floatgen)
        subprop_patchmerge (gen_ReplaceOnly Gen.bool)
        subprop_patchmerge (fromFDEGen $ gen_ListX $ toFDEGen $ gen_ReplaceOnly floatgen)

tests :: IO Bool
tests = checkSequential $$(discover)

main :: IO Bool
main = tests