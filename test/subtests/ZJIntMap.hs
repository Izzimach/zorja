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
            let -- generate an (index,value) tuple
                valuegen = do
                    ix <- indexgen
                    value <- g
                    return (ix, ZJData value)
                -- generate some emptys for testing purposes
                -- (key, ZJEmpty) should be equivalent to not having the
                -- key in the map at all.
                emptygen = do
                    ix <- indexgen
                    return (ix, ZJEmpty)
            in do
                 -- generate some values and some empties, then combine them
                 vs <- Gen.list (Range.linear 0 20) valuegen
                 emptys <- Gen.list (Range.linear 0 5) emptygen
                 let z = (M.fromList (vs ++ emptys))
                 return (ZJIM z)
        ,
        genFDelta = \(ZJIM as) ->
            -- in general there should be a delta for every value in the original, but
            -- some special cases are still valid, so we should handle them all:
            --  - a value 'ZJData a' with patch 'ZJDelta a'
            --  - a value 'ZJData a' with patch 'ZJDelete'
            --  - a value 'ZJData a' with a missing patch (equivalent to nopatch)
            --  - a value 'ZJEmpty'  with patch 'ZJAdd a'
            --  - a value 'ZJEmpty'  with a missing patch
            --  - a missing value    with patch 'ZJAdd a' (missiong value is equivalent to 'ZJEmpty') 
            --
            -- some values that are discarded:
            --  - a missing value with patch 'ZJDelete' /is discarded/
            --  - a missing value with patch 'ZJDelta a' /is discarded/
            do  jx <- traverse genDelta as
                -- jx is an intmap with (Maybe a) as values, need to
                -- clear out the Nothings before returning
                let x = (M.mapMaybe id jx)
                return $ ZJIMD x
    }
    where
        indexgen = Gen.integral (Range.linear (-50) 50)
                
        -- for some value in the original map, generate an add, delete, or delta
        -- as appropriate
        genDelta (ZJData a) =
            Gen.frequency [
                -- sometimes delete, sometimes patch, sometimes missing
                (10, do da <- (dg a)
                        return $ Just $ ZJDelta da),
                (1, return $ Just ZJDelete),
                (1, return Nothing)
            ]
        genDelta ZJEmpty    =
            Gen.frequency [
                -- sometimes add, sometimes missing
                (10, do a <- g
                        return $ Just $ ZJAdd a),
                (1, return Nothing)
            ]

