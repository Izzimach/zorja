{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}


module Zorja.Collections.FAlgebra where

import Zorja.Patchable
import Zorja.ZHOAS
import Zorja.Collections.Spliceable

import Data.Functor.Identity
import Data.IntSet (IntSet)
import qualified Data.IntSet as S
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.IntMap.Strict (IntMap, (\\))
import qualified Data.IntMap.Strict as M
import Data.Distributive
import Data.Functor.Foldable

import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree


{-
zdCata :: (StructurePatchable a, StructurePatchable t, 
           Patchable (Base t a), Patchable (Base t t))
    => (ZDExpr (t -> Base t t))      -- ^ projection
    -> (ZDExpr (Base t a -> a))      -- ^ f-algebra
    -> ZDExpr (t -> a)
zdCata zdproject g = undefined
    -- the original cata was @c where c = g . fmap c . project@

ttg :: Cofree -> ZDVecTree
ttg xs = ZDBranch (ZJVec $ M.fromList $ zip [0..] xs)

testTree :: ZDVecTree
testTree = 
    ttg [
        ZDLeaf (DNum 5),
        ttg [
            ZDLeaf (DNum 6),
            ZDLeaf (DNum 2)
        ]
    ]

testTreeD :: ZDVecTreeD
testTreeD = ZDBranchD (ZJVecD $ M.fromList $ 
        [
            (0,ZJVDelete),
            (1,ZJVPatch $ ZDBranchD (ZJVecD $ M.fromList $
                [
                    (0,ZJVPatch $ ZDLeafD (DNum 2)),
                    (1,ZJVPatch $ ZDLeafD (DNum 13))
                ]
                )
            ),
            (2, ZJVUpsert $ ZDLeaf (DNum 13))
        ]
    )


testCata = app $ zdCata vecTreeProject vecTreeDAlg

testCataArg = (ZDV testTree testTreeD)

testCataSmolArg = (ZDV (ZDLeaf (DNum 6)) (ZDLeafD (DNum 6)) )
-}

