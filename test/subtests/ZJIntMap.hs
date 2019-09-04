{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Subtests.ZJIntMap where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


import Control.Monad

import qualified Data.IntMap.Strict as M


import Zorja.Patchable
import Zorja.Primitives
import Zorja.Collections.ZJIntMap

import Subtests.PatchGen

-- | Generate a ZJItemMap value and delta
gen_ZJItemMap :: FunctorDExprGen f a -> FunctorDExprGen (ZJItemMap f) a
gen_ZJItemMap (FDEGen g dg) =
    FDEGen
    {
        genFValue =
            let indexgen = Gen.integral (Range.linear (-50) 50)
                valuegen = do
                    -- first generate an index, then a value
                    ix <- indexgen
                    value <- g
                    return (ix, ZJData value)
                -- generate some emptys for testing
                emptygen = do
                    ix <- indexgen
                    return (ix, ZJEmpty)
            in do
                 vs <- Gen.list (Range.linear 0 20) valuegen
                 emptys <- Gen.list (Range.linear 0 5) emptygen
                 let z = (M.fromList (vs ++ emptys))
                 return (ZJIM z)
        ,
        genFDelta = \(ZJIM as) ->
            do  x <- mapM genDelta as
                return $ ZJIMD x
    }
    where
        genDelta (ZJData a) = Gen.frequency [
                                  -- sometimes delete, sometimes patch
                                  (10, do da <- (dg a)
                                          return $ ZJDelta da),
                                  (1, return ZJDelete)
                              ]
        genDelta ZJEmpty    = do a <- g
                                 return $ ZJAdd a

