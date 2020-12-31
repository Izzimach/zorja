{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Zorja.PatchableTest where

import qualified Data.Text as T

import Hedgehog
import qualified Hedgehog.Gen as Gen

import Zorja.Patchable


data PatchableGen a = PatchableGen 
  {
    value:: Gen a,
    delta:: a -> Gen (ValDelta a)
  }

genVD :: PatchableGen a -> Gen (ValDelta a)
genVD (PatchableGen g dg) = g >>= dg

mkMaybeGen :: (Patchable a) => PatchableGen a -> PatchableGen (Maybe a)
mkMaybeGen p@(PatchableGen g dg) =
    PatchableGen
    {
        value = genMaybe,
        delta = \a ->
            do
              a' <- genMaybe
              return $ diffBundle a a'
    }
  where
      genMaybe = Gen.choice [fmap Just g, return Nothing]

-- | Patching with a null patch should not change the value
subprop_nullpatch ::
    (Eq a, Show a, Patchable a)
        => PatchableGen a -> PropertyT IO ()
subprop_nullpatch (PatchableGen g _) =
    do
        a <- forAll g
        a === (patch (valueBundle a))           

-- | A subprop used to build props for specific types/structures.
--   Check that patch merges work, so that patching with
--   'da3 = mergepatch da1 da2' produces the same result as
--   patching with 'da1' and then 'da2'.
--
--  'patch (bundleVD (bundleVD (a,da1)),da2) == patch a da3' where 'da3 = mergepatches da1 da2'
--

subprop_patchmerge :: 
    (Eq a, Show a, Show (ValDelta a), Patchable a)
        => PatchableGen a -> PropertyT IO ()
subprop_patchmerge (PatchableGen g dg) =
    do
        -- generate start value and delta, x0 + dx0
        x0   <- forAll g
        xx0  <- forAll (dg x0)
        -- generate the next stage, x1 + dx1
        let x1 = patch xx0
        xx1  <- forAll (dg x1)
        -- generate the final value, x2
        let x2 = patch xx1
        -- combine the two patches to get a big patch from x0 to x2
        let (_,dx0) = unbundleVD xx0
        let (_,dx1) = unbundleVD xx1
        let dx01 = mergePatches dx0 dx1
        (x2) === (patch $ bundleVD (x0,dx01))


-- | A test for patches/changes, if we patch 'a' with 'changes a b' the
--  result should be 'b'
subprop_patchchanges ::
    (Eq a, Show a, Patchable a)
        => PatchableGen a -> PropertyT IO ()
subprop_patchchanges (PatchableGen g _) =
    do
        a   <- forAll g
        b   <- forAll g
        -- check diffs generated with both 'changes' and 'diffBundle'
        let aa1 = bundleVD (a, changes a b)
        ((patch aa1) === b)
        let aa2 = diffBundle a b
        ((patch aa2) === b)
