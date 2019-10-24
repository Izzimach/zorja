{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Zorja.Collections.ZJIntMap 
    (
        ZJIntMap (..),
        ZJItemMap (..),
        ZJItemMapD (..),
        ZJItem (..),
        ZJPatch (..),
        zjItemMapFromList,
        zjItemMapDFromList
    ) where

import Data.Monoid
import Data.Traversable
import Data.Distributive

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as M

import Zorja.Patchable
import Zorja.ZHOAS
import Zorja.FunctorDExpr


--
-- | A fake list/vector using maps with 'Int' keys. Values are
--  wrapped in a functor @f@, to make this compatible with 'FunctorDelta'.
--  You can use any functor for @f@ but typically you would use 'ZJItem'
--

newtype ZJIntMap f a = ZJI (M.IntMap (f a))
    deriving (Eq)
    deriving (Semigroup, Monoid) via (M.IntMap (f a))

instance (Show (f a)) => Show (ZJIntMap f a) where
    show (ZJI a) = "(ZJI " ++ show (M.toList a) ++ ")"

type instance (PatchDelta (ZJIntMap f a)) = ZJIntMap (FunctorDelta f) a
type instance (FunctorDelta (ZJIntMap f)) = ZJIntMap (FunctorDelta f)

instance (PatchInstance (f a)) => PatchInstance (ZJIntMap f a) where
    mergepatches (ZJI a) (ZJI b) = undefined

    nopatch = undefined

instance (Functor f) => Functor (ZJIntMap f) where
    fmap f (ZJI m) = ZJI $ M.map (fmap f) m

instance (Patchable (f a), PatchInstance (FunctorDelta f a)) => Patchable (ZJIntMap f a) where
    patch (ZJI a) (ZJI da) = undefined

    changes (ZJI a) (ZJI a') = undefined

--
-- ZJItem and ZJPatch
--


-- | 'ZJItem' represents a possible value like 'Maybe' but it combines
--  with 'ZJPatch' to produce a full 'FunctorDExpr' where you can add and
--  delete elements.
data ZJItem f a = 
      ZJEmpty 
    | ZJData (f a)
    deriving (Eq, Show)

instance (Functor f) => Functor (ZJItem f) where
    fmap _ ZJEmpty     = ZJEmpty
    fmap f (ZJData a) = ZJData (fmap f a)

instance (Applicative f) => Applicative (ZJItem f) where
    pure x = ZJData $ pure x
    ZJEmpty     <*> _          = ZJEmpty
    _           <*> _          = ZJEmpty
    (ZJData fa) <*> (ZJData b) = ZJData (fa <*> b)

data ZJPatch f a = 
      ZJDelta (FunctorDelta f a)
    | ZJAdd (f a)
    | ZJDelete

instance (Eq (f a), Eq (FunctorDelta f a)) => Eq (ZJPatch f a) where
    (ZJAdd a) == (ZJAdd b)         = (a == b)
    ZJDelete == ZJDelete           = True
    (ZJDelta da) == (ZJDelta db)   = (da == db)
    _            == _              = False

instance (Show (f a), Show (FunctorDelta f a)) => Show (ZJPatch f a) where
    show (ZJAdd a) = "ZJAdd " ++ show a
    show (ZJDelete) = "ZJDelete"
    show (ZJDelta da) = "ZJDelta " ++ show da

instance (Functor f, Functor (FunctorDelta f), FDEFunctor f) => Functor (ZJPatch f) where
    fmap f (ZJDelta da) = ZJDelta $ fmap f da
    fmap f (ZJAdd a) = ZJAdd (fmap f a)
    fmap _ ZJDelete  = ZJDelete
    
type instance (PatchDelta (ZJItem f a)) = ZJPatch f a
type instance (FunctorDelta (ZJItem f)) = ZJPatch f

instance (FDEFunctor f,
          FDECompatible f,
          FDEConvertible f a, 
          Patchable (f a),
          PatchInstance (FunctorDelta f a))
            => PatchInstance (ZJPatch f a) where
    mergepatches (ZJDelta da0) (ZJDelta da1) = ZJDelta (mergepatches da0 da1)
    mergepatches (ZJAdd     a) (ZJDelta da)  = ZJAdd $ patch a (fromFD da)
    mergepatches (ZJDelete)    (ZJDelta _)   = ZJDelete
    -- add and delete just replace whatever came before
    mergepatches _             (ZJAdd da1)   = ZJAdd da1
    mergepatches _             (ZJDelete)    = ZJDelete

    nopatch = ZJDelta nopatch

instance (FDEFunctor f,
          FDECompatible f,
          FDEConvertible f a,
          PatchInstance (FunctorDelta f a),
          Patchable (f a))
            => Patchable (ZJItem f a) where
    patch _           (ZJAdd a)    = ZJData a
    patch ZJEmpty     _            = ZJEmpty
    patch (ZJData _)  ZJDelete     = ZJEmpty
    patch (ZJData a)  (ZJDelta da) = ZJData (patch a (fromFD da))

    changes ZJEmpty     ZJEmpty      = ZJDelta nopatch
    changes ZJEmpty     (ZJData a)   = ZJAdd a
    changes (ZJData _)  ZJEmpty      = ZJDelete
    changes (ZJData a)  (ZJData a')  = ZJDelta $ toFD (changes a a')

instance (FDEFunctor f) => FDECompatible (ZJItem f) where
    type FDEConstraint (ZJItem f) a = 
        (FDECompatible (ZJItem f),
         FDEConvertible f a,
         Patchable (f a),
         PatchInstance (FunctorDelta f a))

    toFDE z = let (v,dv) = zdEval z in FDE v dv
    fromFDE (FDE v dv) = ZDV v dv

    toFD z = z
    fromFD z = z

instance (Functor f, Functor (FunctorDelta f), FDEFunctor f) => FDEFunctor (ZJItem f) where
    fmapFDE f (FDE a da) = FDE (fmap f a) (fmap f da)

instance (FDEFunctor f, FDEDistributive f) => FDEDistributive (ZJItem f) where
    distributeFDE (ZJEmpty)  = FDE ZJEmpty ZJDelete
    distributeFDE (ZJData x) = let (FDE v dv) = distributeFDE x
                               in
                                   FDE (ZJData v) (ZJDelta dv)
        
instance (FDETraversable f, FDEFunctor f, FDECompatible f)
        => FDETraversable (ZJItem f) where
    sequenceFDE (FDE fa dfa) = buwbuw fa dfa
        where
            buwbuw _           (ZJAdd a)    = ZJData $ sequenceFDE (FDE a nopatch)
            buwbuw ZJEmpty     _            = ZJEmpty
            buwbuw (ZJData _)  ZJDelete     = ZJEmpty
            buwbuw (ZJData a)  (ZJDelta da) = ZJData $ sequenceFDE (FDE a da)



--
-- ZJItemMap and ZJItemMapD
--

    
-- | An 'Intmap' with 'ZJItem' as a wrapping functor has the ability
--   to distribute and properly handle adding and removing elements.
newtype ZJItemMap f a = ZJIM (M.IntMap (ZJItem f a))
    deriving (Show)
    deriving (Semigroup, Monoid) via (M.IntMap (ZJItem f a))

instance (Eq (f a)) => Eq (ZJItemMap f a) where
    (ZJIM as) == (ZJIM bs) =
        -- filter out ZJEmpty values, which are equivalent to missing values
        let as' = M.filter (/= ZJEmpty) as
            bs' = M.filter (/= ZJEmpty) bs
        in
            as' == bs'

instance (Functor f) => Functor (ZJItemMap f) where
    fmap f (ZJIM vs) = ZJIM $ fmap (fmap f) vs

newtype ZJItemMapD f a = ZJIMD (M.IntMap (ZJPatch f a))
    deriving ()
    deriving (Semigroup, Monoid) via (M.IntMap (ZJPatch f a))

instance (Eq (ZJPatch f a), PatchInstance (FunctorDelta f a)) => Eq (ZJItemMapD f a) where
    (ZJIMD as) == (ZJIMD bs)    =
        -- filter out nopatch values, which are equivalent to missing values
        let as' = M.filter (/= (ZJDelta nopatch)) as
            bs' = M.filter (/= (ZJDelta nopatch)) bs
        in
            as' == bs'

instance (Show (ZJPatch f a)) => Show (ZJItemMapD f a) where
    show (ZJIMD a) = "(ZJIMD " ++ show a ++ ")"

instance (Functor f, Functor (FunctorDelta f), FDEFunctor f) => Functor (ZJItemMapD f) where
    fmap f (ZJIMD vs) = ZJIMD $ fmap (fmap f) vs



type instance PatchDelta (ZJItemMap f a) = ZJItemMapD f a
type instance FunctorDelta (ZJItemMap f) = ZJItemMapD f

instance (FDEFunctor f,
          FDEConvertible f a,
          Patchable (f a),
          PatchInstance (FunctorDelta f a),
          PatchInstance (ZJItemMapD f a)) 
              => Patchable (ZJItemMap f a) where
    patch (ZJIM a) (ZJIMD da) = ZJIM (M.mergeWithKey both values deltas a da)
        where
            both key v dv = case (patch v dv) of
                               ZJEmpty  -> Nothing
                               ZJData x -> Just $ ZJData x
            -- a missing delta is considered equivalent to 'nopatch'
            -- so we keep these unchanged
            values v      = v
            -- data only in the delta map, a "ZJEmpty" value is implied
            -- so we keep only adds
            deltas dv     = M.mapMaybe onlyAdds dv
                where onlyAdds (ZJAdd x)   = Just $ ZJData x
                      onlyAdds (ZJDelta _)  = Nothing
                      onlyAdds ZJDelete     = Nothing
            

    changes (ZJIM a) (ZJIM a') = ZJIMD (M.mergeWithKey diff inFirst inSecond a a')
        where
            -- if items are in both a an a' we just diff them
            diff _key v v' = Just $ changes v v'
            -- items in a are deleted so they aren't in a'
            inFirst x    = M.mapMaybe (\case
                                           ZJEmpty -> Nothing
                                           ZJData _ -> Just ZJDelete) x
            -- items not in a are added so they are in a'
            inSecond x'  = M.mapMaybe (\case
                                           ZJEmpty -> Nothing
                                           ZJData y -> Just (ZJAdd y)) x'

instance (FDEFunctor f, 
          FDEConvertible f a,
          Patchable (f a),
          PatchInstance (FunctorDelta f a)) => PatchInstance (ZJItemMapD f a) where
    mergepatches (ZJIMD da1) (ZJIMD da2) = ZJIMD (M.unionWith mergepatches da1 da2)

    nopatch = ZJIMD M.empty

instance (FDEFunctor f) => FDECompatible (ZJItemMap f) where
    type FDEConstraint (ZJItemMap f) a = (FDEConvertible f a,
                                          FDEFunctor f,
                                          Patchable (f a),
                                          PatchInstance (FunctorDelta f a))

    toFDE z = let (v,dv) = zdEval z
              in FDE v dv
    fromFDE (FDE a da) = ZDV a da

    toFD z = z
    fromFD z = z

instance (Functor f, Functor (FunctorDelta f), FDEFunctor f) => FDEFunctor (ZJItemMap f) where
    fmapFDE f (FDE v dv) = FDE (fmap f v) (fmap f dv)

instance (FDEFunctor f, FDEDistributive f) => FDEDistributive (ZJItemMap f) where
    --distributeFDE :: (FDEConstraint (ZJItemMap f) (fa a)) => ZJItemMap f (FunctorDExpr fa a) -> FunctorDExpr (ZJItemMap f (fa a))
    distributeFDE (ZJIM x) = let x' = M.map distributeFDE x
                                 v = M.map (\(FDE a _) -> a) x'
                                 dv = M.map (\(FDE _ da) -> da) x'
                             in
                                 FDE (ZJIM v) (ZJIMD dv)

instance (FDEFunctor f, FDETraversable f) => FDETraversable (ZJItemMap f) where
    sequenceFDE (FDE (ZJIM a) (ZJIMD da)) =
        ZJIM $ M.mergeWithKey both onlyValues onlyDeltas a da
        where
            both _key v dv = Just $ sequenceFDE $ FDE v dv
            -- no delta implies a "nochange" delta
            onlyValues vs = M.map (\x -> sequenceFDE (FDE x nopatch)) vs
            -- no value implies it starts ZJEmpty
            onlyDeltas dvs = M.map (\x -> sequenceFDE (FDE ZJEmpty x)) dvs

instance (Foldable f) => Foldable (ZJItemMap f) where
    foldMap f (ZJIM a) = foldMap f' a
        where
            f' (ZJData a) = foldMap f a
            f' (ZJEmpty)  = mempty

zjItemMapFromList :: [f a] -> ZJItemMap f a
zjItemMapFromList l = ZJIM $ M.fromList $ zip [1..] (fmap ZJData l)

zjItemMapDFromList :: [FunctorDelta f a] -> [f a] -> ZJItemMapD f a
zjItemMapDFromList patches adds =
    let combinedchanges = (fmap ZJDelta patches) ++ (fmap ZJAdd adds)
    in
        ZJIMD $ M.fromList $ zip [1..] combinedchanges
