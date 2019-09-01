{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (
    main
    ) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


import Zorja.Patchable
import Zorja.Primitives

--
-- | Patch generator: can generate a value of type 'a' which is 'Patchable'
--  and also given an 'a' can generate a 'PatchDelta a' value for that
--  value
--
data PatchableGen a = PatchableGen
    {
        genValue :: Gen a,
        genDelta :: a -> Gen (PatchDelta a)
    }

--
-- | Generator for the ReplaceOnly primitive.  Given a value generator
--  this will produce something to generate values and deltas.
--
replaceOnlyGenerator :: Gen a -> PatchableGen (ReplaceOnly a)
replaceOnlyGenerator g =
    PatchableGen
    {
        genValue = fmap ReplaceOnly g,
        genDelta = \_ -> Gen.frequency
            [
                (1, (Gen.constant $ Replacing Nothing)),
                (3, fmap (Replacing . Just) g)
            ]
    }


patchmerge_onetype :: 
    (Eq a, Show a, Show (PatchDelta a), Patchable a)
        => PatchableGen a -> PropertyT IO ()
patchmerge_onetype (PatchableGen g dg) =
    do
        x   <- forAll g
        dx1 <- forAll (dg x)
        dx2 <- forAll (dg (patch x dx1))
        (patch (patch x dx1) dx2) === (patch x (mergepatches dx1 dx2))

prop_patchmerge :: Property
prop_patchmerge = 
    property $ do
        let intgen   = Gen.integral $ Range.linear (0::Integer) (100::Integer)
        let floatgen = Gen.float $ Range.linearFrac (0.0::Float) (100.0::Float)
        patchmerge_onetype (replaceOnlyGenerator intgen)
        patchmerge_onetype (replaceOnlyGenerator floatgen)
        patchmerge_onetype (replaceOnlyGenerator Gen.bool)


tests :: IO Bool
tests = checkSequential $$(discover)

main :: IO Bool
main = tests