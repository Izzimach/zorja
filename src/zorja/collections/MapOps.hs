{-# LANGUAGE TypeFamilies #-}

module Zorja.Collections.MapOps where

import qualified Data.Map as M

import Zorja.Patchable
import Zorja.Primitives


newtype MapOps k a = MapOps (M.Map k a)

newtype MapOpsDelta k a = MapOpsDelta (M.Map k (MapOp a))

data MapOp a =
      Patch (ILCDelta a)
    | Insert a
    | Delete

data MapOpsValDelta k a = MapOpsValDelta (M.Map k a) (M.Map k (MapOp a))


type instance ILCDelta (MapOps k a) = MapOpsDelta k a
type instance ValDelta (MapOps k a) = MapOpsValDelta k a

empty :: MapOpsValDelta k a
empty = MapOpsValDelta (M.empty) (M.empty)

insert :: (Ord k, Patchable a) => k -> a -> MapOpsValDelta k a -> MapOpsValDelta k a
insert k v (MapOpsValDelta a da) = 
    let delta = case (M.lookup k a) of
                    Nothing -> Insert v
                    Just x  -> Patch (changes v x)
    in
        MapOpsValDelta a (M.insert k delta da)

delete :: (Ord k) => k -> MapOpsValDelta k a -> MapOpsValDelta k a
delete k (MapOpsValDelta a da) = MapOpsValDelta a (M.insert k Delete da)

foldMap :: (Ord k, Monoid m) => (a -> m) -> MapOpsValDelta k a -> m
foldMap f (MapOpsValDelta a da) = undefined
