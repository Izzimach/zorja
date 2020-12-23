

module Zorja.Collections.SpliceableTest where

import Hedgehog
import Hedgehog.Gen
import Hedgehog.Range

import Zorja.Patchable
import Zorja.Primitives

import Zorja.BasicGenerators
import Zorja.PatchableTest
import Zorja.PrimitivesTest
import Zorja.Collections.Spliceable (SplicedList(..), SplicedListValDelta(..))
import qualified Zorja.Collections.Spliceable as SP

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
runRandomListOp _p@(PatchableGen g _dg) l =
  do
    let s = SP.length l
    if (s < 1)
    -- if the list is empty we either do nothing or insert an element
    then choice
      [
        (do
          v <- g
          return (SP.cons v l)),
        (return l)
      ]
    -- for non-empty lists we can take/drop/insert/cons elements,
    -- or simply modify an element
    else choice
      [
        (do
          c <- int $ linear 0 s
          return (SP.take c l)),
        (do
          c <- int $ linear 0 s
          return (SP.drop c l)),
        (do
          c <- int $ linear 0 s
          v <- g
          return (SP.insertAt c v l)),
        (do
          v <- g
          return (SP.cons v l)),
        (return l)
      ]

