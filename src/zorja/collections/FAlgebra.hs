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
-- So changes to the tree are transformed into splice actions on the folded
-- result.
--
{-
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
-}

--
-- A fake list/vector using maps with @Int@ keys. 
--

newtype ZJVector a = ZJVec (M.IntMap a)
    deriving (Eq)

instance (Show a) => Show (ZJVector a) where
    show (ZJVec a) = "(ZJVec " ++ show (M.toList a) ++ ")"

data ZJVectorOp a =
      ZJVDelete
    | ZJVUpsert a
    | ZJVPatch (PatchDelta a)

instance (Eq a, Eq (PatchDelta a)) => Eq (ZJVectorOp a) where
    ZJVDelete == ZJVDelete     =  True
    ZJVUpsert a == ZJVUpsert b =  a == b
    ZJVPatch da == ZJVPatch db =  da == db

instance (Show a, Show (PatchDelta a)) => Show (ZJVectorOp a) where
    show ZJVDelete = "<ZJVDelete>"
    show (ZJVUpsert a) = "<ZJVUpsert " ++ show a ++ ">"
    show (ZJVPatch da) = "<ZJVPatch " ++ show da ++ ">"

newtype ZJVectorD a = ZJVecD (M.IntMap (ZJVectorOp a))

instance (Eq a, Eq (PatchDelta a)) => Eq (ZJVectorD a) where
    (ZJVecD a) == (ZJVecD b)  = a == b

instance (Show a, Show (PatchDelta a)) => Show (ZJVectorD a) where
    show (ZJVecD a) = "(ZJVecD " ++ show (M.toList a) ++ ")"

type instance (PatchDelta (ZJVector a)) = ZJVectorD a

instance (Patchable a) => Semigroup (ZJVectorOp a) where
    -- upsert and delete replace previous operations
    _ <> ZJVDelete = ZJVDelete
    _ <> ZJVUpsert a = ZJVUpsert a
    -- patches get mmerged
    ZJVPatch da0 <> ZJVPatch da1 = ZJVPatch (da0 <> da1)
    -- we don't want a ZDVectorOp to hold both an update AND a patch, so
    -- merge update with patch by simply applying the patch
    ZJVUpsert a <> ZJVPatch da = ZJVUpsert (patch a da)
    -- delete then patch. there's nothing to patch so ignore the patch
    ZJVDelete <> ZJVPatch da = ZJVDelete

instance (Patchable a) => Semigroup (ZJVectorD a) where
    (ZJVecD m0) <> (ZJVecD m1) = ZJVecD (M.unionWith (<>) m0 m1)

instance (Patchable a) => Monoid (ZJVectorD a) where
    mempty = ZJVecD M.empty


instance (Patchable a) => Patchable (ZJVector a) where
    patch (ZJVec a) (ZJVecD da) = ZJVec $ M.foldrWithKey f a da
        where
            f k op a' = case op of
                           ZJVDelete -> M.delete k a'
                           ZJVUpsert x -> M.insert k x a'
                           ZJVPatch dx -> M.adjust (\x -> patch x dx) k a'

    changes (ZJVec a) (ZJVec a') =
        -- need to handle all three ops:
        --   elements in @a@ but not in @a'@ are @ZJVDelete@s
        --   elements in @a'@ but not in @a@ are @ZJVUpsert@s
        --   elements in both are @ZJVPatch@s
        let patches = M.intersectionWith (\v v' -> ZJVPatch (changes v v')) a a'
            inserts = M.map ZJVUpsert         $ M.difference a  a'
            deletes = M.map (const ZJVDelete) $ M.difference a' a
        in
            ZJVecD (deletes `M.union` inserts `M.union` patches)

--
-- Merge a @ZJVector a@ and a @ZJVectorD a@ into a single map of
-- @ZDExpr a@s
--
zVecMerge :: (StructurePatchable a) => ZJVector a -> ZJVectorD a -> ZJVector (ZDExpr a)
zVecMerge (ZJVec zv) (ZJVecD zvd) = 
    -- convert the original value into a map of ZDExprs with no deltas
    let zve = M.map (\x -> ZDV x mempty) zv
        -- next apply vector ops and update values accordingly
    in
        ZJVec $ M.foldrWithKey f zve zvd
    where
        f :: (StructurePatchable a) => Int -> ZJVectorOp a -> M.IntMap (ZDExpr a) -> M.IntMap (ZDExpr a)
        f k op zve = case op of
                        -- convert the ZDExpr into a delete ZDExpr using StructurePatchable
                         ZJVDelete -> M.adjust (\(ZDV a _) -> fromSDExpr (SDDelete a)) k zve
                         ZJVUpsert x' -> M.alter (alterUpsert x') k zve
                         -- accumulate in the patch. If no key is found the patch will be thrown away
                         ZJVPatch dx -> M.adjust (\(ZDV a da) -> ZDV a (da <> dx)) k zve
        -- if there was previously no value for this key, it's an add. If not,
        -- generate a patch to switch to the new value.
        alterUpsert x' v = case v of
                               Nothing -> Just $ fromSDExpr (SDAdd x')
                               Just (ZDV x dx) -> Just $ ZDV x (dx <> (changes x x'))

--
-- Quasi-distributive law for ZDExpr / ZJVector
--
zdVecDistribute :: (StructurePatchable a) => ZDExpr (ZJVector a) -> ZJVector (ZDExpr a)
zdVecDistribute zx = let (a,da) = zdEval zx
                     in zVecMerge a da

--
-- Quasi-traverse for ZDExpr / ZJVector
--
zdVecSequence :: (StructurePatchable a) => ZJVector (ZDExpr a) -> ZDExpr (ZJVector a)
zdVecSequence (ZJVec zj) = let zjSD = M.map toSDExpr zj
                               emptyZJVec = ZDV (ZJVec M.empty) (ZJVecD M.empty)
                           in
                               M.foldrWithKey processSDExpr emptyZJVec zjSD
    where
        processSDExpr :: (StructurePatchable a) => 
            Int -> SDExpr a -> ZDExpr (ZJVector a) -> ZDExpr (ZJVector a)
        processSDExpr key op (ZDV (ZJVec vals) (ZJVecD ops)) =
            -- convert SDExpr into the corresponding vector op
            case op of
                (SDJust za)  -> let (x,dx) = zdEval za 
                                in ZDV (ZJVec (M.insert key x vals)) (ZJVecD (M.insert key (ZJVPatch dx) ops))
                (SDDelete a) ->    ZDV (ZJVec (M.insert key a vals)) (ZJVecD (M.insert key (ZJVDelete) ops))
                (SDAdd a)    ->    ZDV (ZJVec vals)                  (ZJVecD (M.insert key (ZJVUpsert a) ops))

zdVecMap :: (StructurePatchable a, StructurePatchable b) =>
    ZDExpr (a -> b) -> ZDExpr (ZJVector a) -> ZDExpr (ZJVector b)
zdVecMap zf zvec = let (ZJVec z') = (zdVecDistribute zvec)
                in
                    zdVecSequence $ ZJVec $ M.map (app zf) z'

instance ZDStructFunctor ZJVector where
    zdstructuremap = zdVecMap

instance ZDDistributive ZJVector where
    zddist = zdVecDistribute


data ZDVecTree =
      ZDZero
    | ZDBranch (ZJVector ZDVecTree)
    | ZDLeaf (DNum Integer)
    deriving (Show)


data ZDVecTreeD =
      ZDNoChange
    | ZDBranchD (ZJVectorD ZDVecTree)
    | ZDLeafD (DNum Integer)
    | ZDReplace (ZDVecTree)
    deriving (Show)

type instance PatchDelta ZDVecTree = ZDVecTreeD

instance Semigroup ZDVecTreeD where
    _ <> ZDReplace t = ZDReplace t
    ZDReplace t <> dt = ZDReplace (patch t dt)
    a <> ZDNoChange = a
    ZDNoChange <> a = a
    ZDBranchD da <> ZDBranchD da' = ZDBranchD (da <> da')
    ZDLeafD da <> ZDLeafD da' = ZDLeafD (da <> da')

    -- if there is a leaf/branch mismatch, discard later changes
    a <> _ = a


instance Monoid ZDVecTreeD where
    mempty = ZDNoChange

instance Patchable (ZDVecTree) where
    patch ZDZero _ = ZDZero
    patch x ZDNoChange = x
    patch _ (ZDReplace t) = t
    patch (ZDBranch b) (ZDBranchD db) = ZDBranch (patch b db)
    patch (ZDLeaf n) (ZDLeafD dn) = ZDLeaf (patch n dn)
    -- discard other combinations
    patch x _ = x

    changes a a' = undefined


instance StructurePatchable (ZDVecTree) where
    fromSDExpr (SDJust za)  = za
    fromSDExpr (SDAdd a)    = ZDV ZDZero (ZDReplace a)
    fromSDExpr (SDDelete a) = ZDV a      (ZDReplace ZDZero)

    toSDExpr zj =
        case (zdEval zj) of
            (ZDZero, ZDReplace (ZDZero)) -> SDJust (ZDV ZDZero ZDNoChange)
            (ZDZero, ZDReplace x)        -> SDAdd x
            (x, ZDReplace (ZDZero))      -> SDDelete x
            (z, dz)                      -> SDJust zj

data ZDVecTreeF x =
      ZDZeroF
    | ZDBranchF (ZJVector x)
    | ZDLeafF (DNum Integer)
    deriving (Eq, Show)

data ZDVecTreeDF x =
      ZDNoChangeF
    | ZDBranchDF (ZJVectorD x)
    | ZDLeafDF (DNum Integer)
    | ZDReplaceF (ZDVecTreeF x)

type instance Base (ZDVecTree) = ZDVecTreeF
type instance Base (ZDVecTreeD) = ZDVecTreeDF

instance (Show a, Show (PatchDelta a)) => Show (ZDVecTreeDF a) where
    show ZDNoChangeF = "(ZDNoChangeF)"
    show (ZDBranchDF (ZJVecD x)) = "ZDBranchDF " ++ show x
    show (ZDLeafDF (DNum x)) = "ZDLeafDF " ++ show x
    show (ZDReplaceF t) = "ZDReplaceF " ++ show t

instance (Patchable x) => Semigroup (ZDVecTreeDF x) where
    a <> ZDNoChangeF = a
    _ <> ZDReplaceF t = ZDReplaceF t
    ZDBranchDF s0 <> ZDBranchDF s1 = ZDBranchDF (s0 <> s1)
    ZDLeafDF i0 <> ZDLeafDF i1 = ZDLeafDF (i0 <> i1)
    -- discard mismatches
    x <> _ = x

instance Functor (ZDVecTreeF) where
    fmap f ZDZeroF = ZDZeroF
    fmap f (ZDLeafF i) = ZDLeafF i
    fmap f (ZDBranchF (ZJVec x)) = ZDBranchF (ZJVec (M.map f x))

type instance PatchDelta (ZDVecTreeF x) = ZDVecTreeDF x
                
instance (Patchable x) => Monoid (ZDVecTreeDF x) where
    mempty = ZDNoChangeF

instance (StructurePatchable x) => Patchable (ZDVecTreeF x) where
    patch x ZDNoChangeF = x
    patch _ (ZDReplaceF t) = t
    patch (ZDBranchF zx) (ZDBranchDF dzx) = ZDBranchF (patch zx dzx)
    patch (ZDLeafF i) (ZDLeafDF di)       = ZDLeafF (patch i di)
    -- other cases are a branch/leaf mismatch, so ignore
    patch x _ = x

    changes ZDZeroF ZDZeroF = ZDNoChangeF
    changes (ZDLeafF a) (ZDLeafF b) = if (a == b)
                                      then ZDNoChangeF
                                      else ZDLeafDF (changes a b)
    changes (ZDBranchF ax) (ZDBranchF bx) = ZDBranchDF (changes ax bx)
    changes _ x = ZDReplaceF x
                                            
instance (StructurePatchable x) => StructurePatchable (ZDVecTreeF x) where
    fromSDExpr (SDJust za)  = za
    fromSDExpr (SDAdd a)    = ZDV ZDZeroF (ZDReplaceF a)
    fromSDExpr (SDDelete a) = ZDV a      (ZDReplaceF ZDZeroF)

    toSDExpr zj =
        case (zdEval zj) of
            (ZDZeroF, ZDReplaceF (ZDZeroF)) -> SDJust (ZDV ZDZeroF ZDNoChangeF)
            (ZDZeroF, ZDReplaceF x)         -> SDAdd x
            (x, ZDReplaceF (ZDZeroF))       -> SDDelete x
            (z, dz)                         -> SDJust zj

zdVecTreeFSequence :: (StructurePatchable a) => ZDVecTreeF (ZDExpr a) -> ZDExpr (ZDVecTreeF a)
zdVecTreeFSequence ZDZeroF = ZDV ZDZeroF ZDNoChangeF
zdVecTreeFSequence (ZDLeafF i) = ZDV (ZDLeafF i) ZDNoChangeF
zdVecTreeFSequence (ZDBranchF zda) = let (z,dz) = zdEval (zdVecSequence zda)
                                     in ZDV (ZDBranchF z) (ZDBranchDF dz)

    
instance ZDStructFunctor ZDVecTreeF where
    zdstructuremap f zt =
        case (zdEval zt) of
            (x, ZDNoChangeF) -> let x' = fmap (\a -> app f (ZDV a mempty)) x
                                in zdVecTreeFSequence x'
            (ZDBranchF x, ZDBranchDF dx) -> let (ZDV x' dx') = zdstructuremap f (ZDV x dx)
                                            in ZDV (ZDBranchF x') (ZDBranchDF dx')
            (ZDLeafF i, ZDLeafDF di) -> ZDV (ZDLeafF i) (ZDLeafDF di)

            (ZDZeroF, ZDReplaceF (ZDZeroF)) -> ZDV ZDZeroF (ZDReplaceF (ZDZeroF))
            -- adds
            (ZDZeroF, ZDReplaceF (ZDLeafF i)) -> ZDV ZDZeroF (ZDReplaceF (ZDLeafF i))
            (ZDZeroF, ZDReplaceF (ZDBranchF (ZJVec xs))) -> 
                let xs' = M.map (\a -> app f (fromSDExpr (SDAdd a))) xs
                    (z,dz) = zdEval $ zdVecSequence (ZJVec xs')
                in ZDV (ZDBranchF z) (ZDBranchDF dz)
            -- deletes
            (ZDLeafF i, ZDReplaceF (ZDZeroF)) -> ZDV (ZDLeafF i) (ZDReplaceF (ZDZeroF))
            (ZDBranchF (ZJVec x), ZDReplaceF (ZDZeroF)) -> 
                let x' = fmap (\a -> app f (fromSDExpr (SDDelete a))) x
                    (z,dz) = zdEval $ zdVecSequence (ZJVec x')
                in ZDV (ZDBranchF z) (ZDBranchDF dz)
            -- fallback, discard patch
            (ZDZeroF, _) -> ZDV ZDZeroF ZDNoChangeF

vecTreeProject :: ZDExpr (ZDVecTree -> ZDVecTreeF ZDVecTree)
vecTreeProject = lam $ \zt ->
    let (z,dz) = zdEval zt
    in
        ZDV (ztProject z) (ztDProject dz)
    where
        ztProject ZDZero = ZDZeroF
        ztProject (ZDBranch s) = ZDBranchF s
        ztProject (ZDLeaf i)   = ZDLeafF i

        ztDProject ZDNoChange = ZDNoChangeF
        ztDProject (ZDBranchD s) = ZDBranchDF s
        ztDProject (ZDLeafD i) = ZDLeafDF i
        ztDProject (ZDReplace t) = ZDReplaceF (ztProject t)

instance (Eq i, Num i) => StructurePatchable (DNum i) where
    fromSDExpr (SDAdd a) = ZDV (DNum 0) a
    fromSDExpr (SDDelete a) = ZDV a (negate a)
    fromSDExpr (SDJust zd) = zd

    toSDExpr ze = case (zdEval ze) of
                      ((DNum 0),x) -> SDAdd x
                      (x,dx) -> if (x + dx == 0)
                                then SDDelete x
                                else SDJust ze
                      
zdAddDNum :: (Num i) => ZDExpr (DNum i) -> ZDExpr (DNum i) -> ZDExpr (DNum i)
zdAddDNum za zb = let (a,da) = zdEval za
                      (b,db) = zdEval zb
                  in
                      ZDV (a+b) (da+db)

vecTreeAlg :: (ZDVecTreeF (DNum Integer) -> DNum Integer)
vecTreeAlg = \case
                  ZDZeroF ->  DNum 0
                  ZDBranchF (ZJVec bs) -> M.foldr (+) (DNum 0) bs
                  ZDLeafF i -> i

vecTreeDAlg :: ZDExpr (ZDVecTreeF (DNum Integer) -> DNum Integer)
vecTreeDAlg = lam $ \ze ->
    case (zdEval ze) of
        (x, ZDNoChangeF) -> ZDV (vecTreeAlg x) (DNum 0)
        (x, ZDReplaceF t) -> let x' = vecTreeAlg x
                             in ZDV x' (changes x' (vecTreeAlg t))
        (ZDBranchF b, ZDBranchDF db) -> 
            let (ZJVec zb) = (zdVecDistribute (ZDV b db))
                zd0 = ZDV (DNum 0) (DNum 0)
            in M.foldr' zdAddDNum zd0 zb
        (ZDLeafF i, ZDLeafDF di) -> ZDV i di
        -- any other is mismatch, so discard the diff
        (x, _) -> ZDV (vecTreeAlg x) (DNum 0)

zdCata :: (StructurePatchable a, StructurePatchable t, 
           Patchable (Base t a), Patchable (Base t t), 
           ZDStructFunctor (Base t))
    => (ZDExpr (t -> Base t t))      -- ^ projection
    -> (ZDExpr (Base t a -> a))      -- ^ f-algebra
    -> ZDExpr (t -> a)
zdCata zdproject g = c 
    -- the original cata was @c where c = g . fmap c . project@
    where c = lam $ (app g) . (zdstructuremap c) . (app zdproject)

ttg :: [ZDVecTree] -> ZDVecTree
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
