{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Zorja.Collections.ZJIntMap 
    (
        ZJIntMap (..),
        ZJIntMapD (..)
    ) where

import Data.Monoid
import Data.Traversable
import Data.Distributive

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as M

import Zorja.Patchable
import Zorja.ZHOAS


--
-- A fake list/vector using maps with @Int@ keys. 
--

newtype ZJIntMap a = ZJI (M.IntMap a)
    deriving (Eq)

instance (Show a) => Show (ZJIntMap a) where
    show (ZJI a) = "(ZJI " ++ show (M.toList a) ++ ")"


data ZJIntMapOp a where
    ZJINoChange :: ZJIntMapOp a
    ZJIDelete :: ZJIntMapOp a
    ZJIUpsert :: a -> ZJIntMapOp a

instance Functor ZJIntMapOp where
    fmap f ZJIDelete = ZJIDelete
    fmap f (ZJIUpsert a) = ZJIUpsert (f a)

instance (Eq a, Eq (PatchDelta a)) => Eq (ZJIntMapOp a) where
    ZJINoChange == ZJINoChange   =  True
    ZJIDelete   == ZJIDelete     =  True
    ZJIUpsert a == ZJIUpsert b   =  a == b
    _           == _             =  False

instance (Show a, Show (PatchDelta a)) => Show (ZJIntMapOp a) where
    show ZJINoChange = "<ZJINoChange>"
    show ZJIDelete = "<ZJIDelete>"
    show (ZJIUpsert a) = "<ZJIUpsert " ++ show a ++ ">"

newtype ZJIntMapD a = ZJID (M.IntMap (ZJIntMapOp a))

instance (Eq a, Eq (PatchDelta a)) => Eq (ZJIntMapD a) where
    (ZJID a) == (ZJID b)  = a == b

instance (Show a, Show (PatchDelta a)) => Show (ZJIntMapD a) where
    show (ZJID a) = "(ZJID " ++ show (M.toList a) ++ ")"

type instance (PatchDelta (ZJIntMap a)) = ZJIntMapD a
type instance (UnPatchDelta (ZJIntMapD a)) = ZJIntMap a

instance (Patchable a) => Semigroup (ZJIntMapOp a) where
    -- upsert and delete replace previous operations
    a <> ZJINoChange = a
    _ <> ZJIDelete = ZJIDelete
    _ <> ZJIUpsert a = ZJIUpsert a

instance (Patchable a) => Semigroup (ZJIntMapD a) where
    (ZJID m0) <> (ZJID m1) = ZJID (M.unionWith (<>) m0 m1)

instance (Patchable a) => Monoid (ZJIntMapD a) where
    mempty = ZJID M.empty

instance Functor (ZJIntMap) where
    fmap f (ZJI m) = ZJI $ M.map f m

instance Functor (ZJIntMapD) where
    fmap f (ZJID m) = ZJID $ M.map (fmap f) m

instance (Patchable a) => Patchable (ZJIntMap a) where
    patch (ZJI a) (ZJID da) = ZJI $ M.foldrWithKey f a da
        where
            f k op a' = case op of
                           ZJINoChange -> a'
                           ZJIDelete -> M.delete k a'
                           ZJIUpsert x -> M.insert k x a'

    changes (ZJI a) (ZJI a') =
        -- need to handle all three ops:
        --   elements in @a@ but not in @a'@ are @ZJIDelete@s
        --   elements in @a'@ but not in @a@ are @ZJIUpsert@s
        --   elements in both are @ZJIUpsert@s
        let upserts = M.map ZJIUpsert         $ (M.difference a  a') `M.union` (M.intersection a a')
            deletes = M.map (const ZJIDelete) $ M.difference a' a
        in
            ZJID (deletes `M.union` upserts)


instance (StructurePatchable a) => StructurePatchable (ZJIntMap a) where
    fromSDExpr (SDF sf) = undefined
    fromSDExpr (SDV a da) = ZDV a da
    -- add is "add all" and delete is "delete all"
    fromSDExpr (SDAdd (ZJI a)) = ZDV (ZJI M.empty) (ZJID $ M.map (\v -> ZJIUpsert v) a)
    fromSDExpr (SDDelete (ZJI a)) = ZDV (ZJI a) (ZJID $ M.map (\_ -> ZJIDelete) a)
            | isAdd a da    = SDAdd x
            | isDelete a da = SDDelete x
            | otherwise     = SDV x dx
        where
            isAdd a da = (null a) && (not (M.null da))
            isDelete a da = (not (M.null a)) && (allDeletes a da)

            -- it's a delete if all elemeents have an associated SDDelete op
            -- in the SJID
            allDeletes :: M.IntMap a -> M.IntMap (ZJIntMapOp a) -> Bool
            allDeletes a da = all (hasDelete da) (M.keys a)

            hasDelete :: M.IntMap (ZJIntMapOp a) -> Int -> Bool
            hasDelete da k = case (M.lookup k da) of
                               Just ZJIDelete -> True
                               _ -> False

instance SDFunctor ZJIntMap where
    sdfmap sf sv = let (ZJI s') = sddistribute sv
                  in
                      sdsequenceA $ ZJI $ M.map sf s'


instance SDDistributive ZJIntMap where
    sddistribute sv =
        -- start with a map containing ZDExprs with no deltas
        let (ZJI v, ZJID dv) = zdEval (fromSDExpr sv)
            sve = M.map (\x -> SDV x mempty) v
            -- next apply add/remove ops and update values accordingly
        in
            ZJI $ M.foldrWithKey f sve dv
        where
            f :: (StructurePatchable a) => Int -> ZJIntMapOp a -> M.IntMap (SDExpr a) -> M.IntMap (SDExpr a)
            f k op sve = case op of
                            ZJINoChange -> sve
                            ZJIDelete -> M.adjust (\(SDV a _) -> (SDDelete a)) k sve
                            ZJIUpsert x' -> M.alter (alterUpsert x') k sve
            -- if there was previously no value for this key, it's an add. If not,
            -- generate a patch to switch to the new value.
            alterUpsert x' v = case v of
                                Nothing -> Just $ SDAdd x'
                                Just sv -> let (x,dx) = zdEval $ fromSDExpr sv
                                               dx' = changes x x'
                                           in Just $ toSDExpr $ ZDV x dx'



instance SDFoldable ZJIntMap where
    sdfoldr = undefined

instance SDTraversable ZJIntMap where
    sdsequenceA (ZJI sj) = let emptyZJI = SDV (ZJI M.empty) (ZJID M.empty)
                     in
                         M.foldrWithKey processSDExpr emptyZJI sj
        where
            processSDExpr :: (StructurePatchable a, UnPatchDelta (PatchDelta a) ~ a) => Int -> SDExpr a -> SDExpr (ZJIntMap a) -> SDExpr (ZJIntMap a)
            processSDExpr key op (SDV (ZJI vals) (ZJID ops)) =
                -- convert SDExpr into the corresponding vector op
                case op of
                    (SDF sf)     -> undefined
                    (SDV x dx)   ->  SDV (ZJI (M.insert key x vals)) (ZJID (M.insert key (ZJIUpsert (patch x dx)) ops))
                    (SDDelete a) ->  SDV (ZJI (M.insert key a vals)) (ZJID (M.insert key (ZJIDelete) ops))
                    (SDAdd a)    ->  SDV (ZJI vals)                  (ZJID (M.insert key (ZJIUpsert a) ops))


--
-- Merge a @ZJIntMap a@ and a @ZJIntMapD a@ into a single map of
-- @ZDExpr a@s
--
zVecMerge :: (StructurePatchable a) => ZJIntMap a -> ZJIntMapD a -> ZJIntMap (ZDExpr a)
zVecMerge (ZJI zv) (ZJID zvd) = 
    -- convert the original value into a map of ZDExprs with no deltas
    let zve = M.map (\x -> ZDV x mempty) zv
        -- next apply vector ops and update values accordingly
    in
        ZJI $ M.foldrWithKey f zve zvd
    where
        f :: (StructurePatchable a) => Int -> ZJIntMapOp a -> M.IntMap (ZDExpr a) -> M.IntMap (ZDExpr a)
        f k op zve = case op of
                        -- convert the ZDExpr into a delete ZDExpr using StructurePatchable
                         ZJINoChange -> sve
                         ZJIDelete -> M.adjust (\(ZDV a _) -> fromSDExpr (SDDelete a)) k zve
                         ZJIUpsert x' -> M.alter (alterUpsert x') k zve
                         -- accumulate in the patch. If no key is found the patch will be thrown away
        -- if there was previously no value for this key, it's an add. If not,
        -- generate a patch to switch to the new value.
        alterUpsert x' v = case v of
                               Nothing -> Just $ fromSDExpr (SDAdd x')
                               Just (ZDV x dx) -> Just $ ZDV x (dx <> (changes x x'))

--
-- Quasi-distributive law for ZDExpr / ZJIntMap
--
zdVecDistribute :: (StructurePatchable a, BijectiveDelta a) => ZDExpr (ZJIntMap a) -> ZJIntMap (ZDExpr a)
zdVecDistribute zx = let (a,da) = zdEval zx
                     in zVecMerge a da

--
-- Quasi-traverse for ZDExpr / ZJIntMap
--
zdVecSequence :: (StructurePatchable a, BijectiveDelta a) => ZJIntMap (ZDExpr a) -> ZDExpr (ZJIntMap a)
zdVecSequence (ZJI zj) = let zjSD = M.map toSDExpr zj
                             emptyZJI = ZDV (ZJI M.empty) (ZJID M.empty)
                         in
                             M.foldrWithKey processSDExpr emptyZJI zjSD
    where
        processSDExpr :: (StructurePatchable a, BijectiveDelta a) => 
            Int -> SDExpr a -> ZDExpr (ZJIntMap a) -> ZDExpr (ZJIntMap a)
        processSDExpr key op (ZDV (ZJI vals) (ZJID ops)) =
            -- convert SDExpr into the corresponding vector op
            case op of
                (SDF sf)     ->    undefined
                (SDV a da)   ->    ZDV (ZJI (M.insert key a vals)) (ZJID (M.insert key (ZJIUpsert (patch a da)) ops))
                (SDDelete a) ->    ZDV (ZJI (M.insert key a vals)) (ZJID (M.insert key (ZJIDelete) ops))
                (SDAdd a)    ->    ZDV (ZJI vals)                  (ZJID (M.insert key (ZJIUpsert a) ops))

zdVecMap :: (StructurePatchable a, BijectiveDelta a, StructurePatchable b, BijectiveDelta b) =>
    ZDExpr (a -> b) -> ZDExpr (ZJIntMap a) -> ZDExpr (ZJIntMap b)
zdVecMap zf zvec = let (ZJI z') = (zdVecDistribute zvec)
                in
                    zdVecSequence $ ZJI $ M.map (app zf) z'


