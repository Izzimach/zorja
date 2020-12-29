module Zorja.Collections.MapValDeltaTest where

import Hedgehog
import Hedgehog.Gen
import Hedgehog.Range

import qualified Data.Map as M

import Zorja.Patchable
import Zorja.Primitives

import Zorja.BasicGenerators
import Zorja.PatchableTest
import Zorja.PrimitivesTest

import Zorja.Collections.MapValDelta as MM

mkMapValDeltaGenerator :: (Patchable a) => PatchableGen a -> PatchableGen (MapValues Integer a)
mkMapValDeltaGenerator p@(PatchableGen g dg) =
    PatchableGen
    {
        value =
          do
            vals <- basic_listgen g
            keys <- traverse (const basic_integergen) vals
            let rawmap = M.fromList (zip keys vals)
            return (MapValues rawmap)
        ,
        delta = \m ->
          do
            let mm = valueBundle m
            let runOp = randomMapOp p
            -- run 1-4 map operations
            choice
              [
                (runOp mm),
                (runOp mm >>= runOp),
                (runOp mm >>= runOp >>= runOp),
                (runOp mm >>= runOp >>= runOp >>= runOp),
              ]
    }

replaceOnlyFloatMapGen :: PatchableGen (MapValues Integer (ReplaceOnly Float))
replaceOnlyFloatMapGen = mkMapValDeltaGenerator replaceOnlyFloatGen

randomMapOp :: (Patchable a) =>
    PatchableGen a -> MapValDelta Integer a -> Gen (MapValDelta Integer a)
randomMapOp p mm =
    if (MM.size mm < 1)
    then insertOp p mm
    else
        choice
          [
            insertOp p mm,
            deleteOp mm,
            modifyOp p mm
          ]
    where
        insertOp (PatchableGen g _dg) mins = do
            newK <- basic_integergen
            newV <- g
            return $ MM.insert newK newV mins

        deleteOp mdel = do
            delK <- element (MM.keys mm)
            return $ MM.delete delK mm

        modifyOp (PatchableGen g dg) mmod = do
            modK <- element (MM.keys mm)
            case (MM.lookup modK mm) of
              Nothing -> return mm
              Just _ ->
                do
                  newValue <- g
                  return $ MM.adjust (const newValue) modK mmod

    
