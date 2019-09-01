{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (
    main
    ) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


--import Zorja.Patchable
--import Zorja.Primitives

import Subtests.Patchable
import Subtests.Primitives

prop_patchmerge :: Property
prop_patchmerge = 
    property $ do
        let intgen   = Gen.integral $ Range.linear (0::Integer) (100::Integer)
        let floatgen = Gen.float $ Range.linearFrac (0.0::Float) (100.0::Float)
        subprop_patchmerge (replaceOnlyGenerator intgen)
        subprop_patchmerge (replaceOnlyGenerator floatgen)
        subprop_patchmerge (replaceOnlyGenerator Gen.bool)


tests :: IO Bool
tests = checkSequential $$(discover)

main :: IO Bool
main = tests