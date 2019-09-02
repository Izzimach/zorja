{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Subtests.PatchGen where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Zorja.Patchable
import Zorja.Primitives
import Zorja.ZHOAS
import Zorja.FunctorDExpr

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

-- | Patch generator for FunctorDExpr's
data FunctorDExprGen f a = FDEGen
    {
        genFValue :: Gen (f a),
        genFDelta :: f a -> Gen (FunctorDelta f a)
    }

fromFDEGen :: (FDECompatible f, FDEConstraint f a) =>
    FunctorDExprGen f a -> PatchableGen (f a)
fromFDEGen (FDEGen g dg) = PatchableGen g (fmap (fmap fromFD) dg)

toFDEGen :: (FDECompatible f, FDEConstraint f a) =>
    PatchableGen (f a) -> FunctorDExprGen f a
toFDEGen (PatchableGen g dg) = FDEGen g (fmap (fmap toFD) dg)

-- | A subprop used to build props for specific types/structures.
--   Check that patch merges work, so that patching with
--   'da3 = mergepatch da1 da2' produces the same result as
--   patching with 'da1' and then 'da2'.
--
--  'patch (a da1) da2 == patch a da3' where 'da3 = mergepatches da1 da2'
--
subprop_patchmerge :: 
    (Eq a, Show a, Show (PatchDelta a), Patchable a)
        => PatchableGen a -> PropertyT IO ()
subprop_patchmerge (PatchableGen g dg) =
    do
        x   <- forAll g
        dx1 <- forAll (dg x)
        dx2 <- forAll (dg (patch x dx1))
        (patch (patch x dx1) dx2) === (patch x (mergepatches dx1 dx2))

-- | Given a PatchableGen will generate a sample value and delta
patchsample :: (Patchable a) => PatchableGen a -> IO (ZDExpr a)
patchsample (PatchableGen g dg) = do
    x  <- Gen.sample g
    dx <- Gen.sample (dg x)
    return $ ZDV x dx
