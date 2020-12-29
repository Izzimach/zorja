

module Zorja.Collections.SplicedListTest where

import Hedgehog
import Hedgehog.Gen
import Hedgehog.Range

import Zorja.Patchable
import Zorja.Primitives

import Zorja.BasicGenerators
import Zorja.PatchableTest
import Zorja.PrimitivesTest
import Zorja.Collections.SplicedList (SplicedList(..), SplicedListValDelta(..))
import qualified Zorja.Collections.SplicedList as SP

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
    -- if the list is empty we insert one or two elements
    then choice
      [
        (do
          v <- g
          return (SP.cons v l)),
        (do
          v1 <- g
          v2 <- g
          return (SP.cons v1 (SP.cons v2 l)))
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
          return (SP.cons v l))
      ]

