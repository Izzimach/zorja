{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module Zorja.Collections.FAlgebra where

import Zorja.Patchable
import Zorja.ZHOAS
import Zorja.Collections.Spliceable

import Data.Functor.Identity
import Data.Functor.Foldable

import Control.Comonad
import Control.Comonad.Cofree

data RoseTree v = 
      RN [RoseTree v]
    | RLeaf v
    deriving (Show)
    
data RoseTreeDelta v =
      RNNoChange
    | RNChanges [RoseTreeDelta v] (PatchDelta v)
    | RNReplace (RoseTree v)


type instance PatchDelta (RoseTree v) = RoseTreeDelta v


instance (Patchable v, Semigroup v, Eq v) => Semigroup (RoseTreeDelta v) where
    a <> RNNoChange = a
    RNNoChange <> b = b
    (RNChanges da0 da1) <> (RNChanges db0 db1) = RNChanges (da0 <> db0) (da1 <> db1)
    RNReplace rt <> x = RNReplace $ patch rt x
    _ <> RNReplace rt = RNReplace rt

instance (Patchable v, Semigroup v, Eq v) => Monoid (RoseTreeDelta v) where
    mempty = RNNoChange

instance (Patchable v, Semigroup v, Eq v) => Patchable (RoseTree v) where
    patch x RNNoChange = x
    patch (RN xs) (RNChanges dxs _) = RN $ zipWith patch xs dxs
    patch (RLeaf v) (RNChanges _ dv) = RLeaf (patch v dv)
    patch _ (RNReplace rt) = rt

    changes (RN []) (RN []) = RNNoChange
    changes (RN x1s) (RN x2s) = RNChanges (zipWith changes x1s x2s) mempty
    changes (RLeaf a) (RLeaf b) = if a == b
                                  then RNNoChange
                                  else RNChanges mempty (changes a b)
    changes _ y = RNReplace y

--
-- functorized equivalents
--

data RoseNodeF v x =
      RNF [x]
    | RLeafF v
    deriving (Show)

instance Functor (RoseNodeF v) where
    fmap f (RNF as) = RNF $ fmap f as
    fmap f (RLeafF d) = RLeafF d

data RoseNodeDeltaF v x =
      RNNoChangeF
    | RNChangesF [x] (PatchDelta v)
    | RNReplaceF (RoseTree v)

instance Functor (RoseNodeDeltaF v) where
    fmap f RNNoChangeF = RNNoChangeF
    fmap f (RNChangesF xs d) = RNChangesF (fmap f xs) d
    fmap f (RNReplaceF rnf) = RNReplaceF rnf


type instance PatchDelta (RoseNodeF v x) = RoseNodeDeltaF v x


--
-- project to functorized version for recursion-schemes
--

type instance Base (RoseTree v) = RoseNodeF v

instance Recursive (RoseTree v) where
    project (RN xs) = RNF xs
    project (RLeaf v) = RLeafF v

instance Corecursive (RoseTree v) where
    embed (RNF xs) = RN xs
    embed (RLeafF v) = RLeaf v



type instance Base (RoseTreeDelta v) = RoseNodeDeltaF v

instance Recursive (RoseTreeDelta v) where
    project RNNoChange = RNNoChangeF
    project (RNChanges xs dx) = RNChangesF xs dx
    project (RNReplace rt) = RNReplaceF rt

instance Corecursive (RoseTreeDelta v) where
    embed RNNoChangeF = RNNoChange
    embed (RNChangesF xs dx) = RNChanges xs dx
    embed (RNReplaceF rt) = RNReplace rt

--
-- | Code to fold a tree into a SpliceArray, with deltas
-- | So changes to the tree are transformed into splice actions on the folded
-- | result.
--

treeToSplice :: (SpliceArray a, Monoid a) => RoseTree a -> RoseTreeDelta a -> ZDExpr a
treeToSplice t dt =
    let txt = foldTree t
        tsize = chunkSize txt
    in case (unfix dt) of
        NoChange -> SPLJ txt []
        Replace b ->  let btxt = foldTree b
                          splice = mkSplice 0 (toInteger tsize) btxt
                      in SPLJ txt [splice]
        LeafChange da -> SPLJ txt (deltaToSplice da)
        BranchChange dl dr -> case (unfix t) of
            (Leaf x) -> undefined
            (Branch l r) ->
                let lxd = treeToSplice l dl
                    rxd = treeToSplice r dr
                in concatSpliceDExpr lxd rxd



--
-- Rose tree & delta as cofree comnads
--


type RoseTree2 a = Cofree [] a

data RoseTreePatch a =
      RoseNoPatch
    | RoseChange (PatchDelta a)
    | RoseReplace a

type RoseTreeDelta2 a = Cofree [] (RoseTreePatch a)

