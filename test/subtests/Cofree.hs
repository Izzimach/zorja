{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Subtests.Cofree where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


import Control.Monad

import Data.Kind
import Data.Functor.Identity

import Zorja.Patchable
import Zorja.Primitives
--import Zorja.Collections.ZJIntMap
import Zorja.Collections.Cofree

import Subtests.PatchGen
import Subtests.Primitives
--import Subtests.ZJIntMap

-- | Generate a CofD tree value and delta
gen_CofDTree :: (Monoid (fb (CofD fb fa a)),
                 Monoid (FunctorDelta fb (CofD fb fa a))) =>
                   FunctorDExprGen fa a  -- ^ generator for the payload
                -> (FunctorDExprGen (CofD fb fa) a -> FunctorDExprGen fb (CofD fb fa a))  -- ^ generator for the branching functor
                -> FunctorDExprGen (CofD fb fa) a
gen_CofDTree fga fgb =
    let ga = genFValue fga
        dga = genFDelta fga
        gen_Branches = genFValue $ fgb $ gen_CofDTree fga fgb
        gen_DeltaBranches = genFDelta $ fgb $ gen_CofDTree fga fgb
    in
        FDEGen
        {
            genFValue = Gen.recursive Gen.choice
                [
                    -- non-recursive generators
                    (:<<) <$> ga <*> mempty
                ]
                [
                    -- recursive generators
                    (:<<) <$> ga <*> gen_Branches
                ]  
            ,
            genFDelta = \(a :<< db) ->
                let da = dga a
                in
                    (:<#) <$> da <*> (gen_DeltaBranches db)
        }


