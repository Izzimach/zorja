
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Subtests.ListX where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


import Zorja.Patchable
import Zorja.Primitives
import Zorja.Collections.ListX

import Subtests.PatchGen

-- | Generate a ListX of elements
gen_ListX :: FunctorDExprGen f a -> FunctorDExprGen (ListX f) a
gen_ListX (FDEGen g dg) =
    FDEGen
    {
        genFValue = fmap ListX (Gen.list (Range.linear 0 20) g),
        genFDelta = \(ListX as) ->
            do x <- traverse dg as
               return $ ListX x
    }
