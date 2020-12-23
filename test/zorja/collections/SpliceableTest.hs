

module Zorja.Collections.SpliceableTest where

import Prelude hiding (take,drop)

import Hedgehog
import qualified Hedgehog.Gen as Gen

import Zorja.Patchable
import Zorja.Primitives

import Zorja.BasicGenerators
import Zorja.PatchableTest
import Zorja.PrimitivesTest
import Zorja.Collections.Spliceable

mkSplicedListGenerator :: (Patchable a) => PatchableGen a -> PatchableGen (SplicedList a)
mkSplicedListGenerator p@(PatchableGen g _dg) =
  PatchableGen
  {
    value = fmap SplicedList (basic_listgen g),
    delta = \a -> runRandomListOp p (valueBundle a)
  }

splicedIntegerListGen :: PatchableGen (SplicedList (DiffNum Integer))
splicedIntegerListGen = mkSplicedListGenerator diffIntegerGen

runRandomListOp :: (Patchable a) 
    => PatchableGen a -> SplicedListValDelta a -> Gen (SplicedListValDelta a)
runRandomListOp _p@(PatchableGen g _dg) l = Gen.choice
  [
    (pure (take 3 l)),
    (pure (drop 3 l)),
    (do
       v <- g
       return (insertAt 2 v l)),
    (do
       v <- g
       return (cons v l))
  ]

