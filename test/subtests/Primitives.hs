{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Subtests.Primitives where

import Hedgehog
import qualified Hedgehog.Gen as Gen

import Data.Functor.Identity

import Zorja.Primitives

import Subtests.PatchGen


gen_Identity :: PatchableGen a -> PatchableGen (Identity a)
gen_Identity (PatchableGen g dg) =
    PatchableGen
    {
        genValue = fmap Identity g,
        genDelta = \(Identity a) -> fmap IdentityD (dg a)
    }

gen_IdentityFDE :: FunctorDExprGen f a -> FunctorDExprGen Identity (f a)
gen_IdentityFDE (FDEGen g dg) =
    FDEGen
    {
        genFValue = fmap Identity g,
        genFDelta = \(Identity a) -> fmap IdentityD (dg a)
    }

--
-- | Generator for the ReplaceOnly primitive.  Given a value generator
--  this will produce something to generate values and deltas.
--
gen_ReplaceOnly :: Gen a -> PatchableGen (ReplaceOnly a)
gen_ReplaceOnly g =
    PatchableGen
    {
        genValue = fmap ReplaceOnly g,
        genDelta = \_ -> Gen.frequency
            [
                (1, (Gen.constant $ Replacing Nothing)),
                (3, fmap (Replacing . Just) g)
            ]
    }

--
-- replaceonly generation given a FDE generator
--
gen_ReplaceOnlyFDE :: FunctorDExprGen f a -> FunctorDExprGen ReplaceOnly (f a)
gen_ReplaceOnlyFDE (FDEGen g _) =
    FDEGen
    {
        genFValue = fmap ReplaceOnly g
        ,
        genFDelta = \_ ->
            -- ReplaceOnly actually doesn't use the delta generator 'dg'
            -- since all deltas are either Nothing or a new value
            Gen.frequency
            [
                (1, Gen.constant $ Replacing Nothing),
                (3, fmap (Replacing . Just) g)
            ]
    }

