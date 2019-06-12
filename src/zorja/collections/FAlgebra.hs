{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module Zorja.Collections.FAlgebra where

import Zorja.Patchable

import Data.Functor.Foldable

data RoseTree = 
      RN [RoseTree]
    | RLeaf Integer
    deriving (Show)

    
data RoseTreeDelta =
      RNNoChange
    | RNChanges [RoseTreeDelta] Integer
    | RNReplace RoseTree


type instance PatchDelta RoseTree = RoseTreeDelta

instance Semigroup (RoseTreeDelta) where
    a <> RNNoChange = a
    RNNoChange <> b = b
    (RNChanges da0 da1) <> (RNChanges db0 db1) = RNChanges (da0 <> db0) (da1 + db1)
    RNReplace rt <> x = RNReplace $ patch rt x
    _ <> RNReplace rt = RNReplace rt

instance Monoid (RoseTreeDelta) where
    mempty = RNNoChange

instance Patchable (RoseTree) where
    patch x RNNoChange = x
    patch (RN xs) (RNChanges dxs _) = RN $ zipWith patch xs dxs
    patch (RLeaf d) (RNChanges _ dd) = RLeaf (d + dd)
    patch _ (RNReplace rt) = rt

    changes (RN []) (RN []) = RNNoChange
    changes (RN x1s) (RN x2s) = RNChanges (zipWith changes x1s x2s) 0
    changes (RLeaf a) (RLeaf b) = if a == b
                                  then RNNoChange
                                  else RNChanges mempty (b - a)
    changes _ y = RNReplace y

--
-- functorized equivalents
--

type family Unpatch x
type instance (Unpatch (RoseNodeDeltaF a)) = RoseNodeF a

data RoseNodeF x =
      RNF [x]
    | RLeafF Integer
    deriving (Show)

instance Functor RoseNodeF where
    fmap f (RNF as) = RNF $ fmap f as
    fmap f (RLeafF d) = RLeafF d

data RoseNodeDeltaF x =
      RNNoChangeF
    | RNChangesF [x] Integer
    | RNReplaceF RoseTree

instance Functor RoseNodeDeltaF where
    fmap f RNNoChangeF = RNNoChangeF
    fmap f (RNChangesF xs d) = RNChangesF (fmap f xs) d
    fmap f (RNReplaceF rnf) = RNReplaceF rnf

type instance PatchDelta (RoseNodeF a) = RoseNodeDeltaF a

--
-- project to functorized version for recursion-schemes
--

type instance Base RoseTree = RoseNodeF
instance Recursive RoseTree where
    project (RN xs) = RNF xs
    project (RLeaf d) = RLeafF d

type instance Base RoseTreeDelta = RoseNodeDeltaF
instance Recursive RoseTreeDelta where
    project RNNoChange = RNNoChangeF
    project (RNChanges xs dx) = RNChangesF xs dx
    project (RNReplace rt) = RNReplaceF rt

