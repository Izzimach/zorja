{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Zorja.Collections.ZJIntMap 
    (
        ZJIntMap (..)
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


-- | 'ZJItem' represents a possible value like 'Maybe' but it combines
--  with 'ZJPatch' to produce a full 'FunctorDExpr' where you can add and
--  delete elements.
data ZJItem f a = ZJEmpty | ZJData (f a)
    deriving (Eq, Show)

instance (Functor f) => Functor (ZJItem f) where
    fmap _ ZJEmpty     = ZJEmpty
    fmap f (ZJData a) = ZJData (fmap f a)

data ZJPatch f a = ZJDelta (FunctorDelta f a) | ZJAdd (f a) | ZJDelete

instance (Eq (f a), Eq (FunctorDelta f a)) => Eq (ZJPatch f a) where
    (ZJAdd a) == (ZJAdd b)         = (a == b)
    ZJDelete == ZJDelete           = True
    (ZJDelta da) == (ZJDelta db)   = (da == db)
    _            == _              = False

instance (Show (f a), Show (FunctorDelta f a)) => Show (ZJPatch f a) where
    show _ = ""

instance (FDEFunctor f) => Functor (ZJPatch f) where
    fmap f (ZJDelta da) = ZJDelta $ fmapFD f da
    fmap f (ZJAdd a) = ZJAdd (fmap f a)
    fmap _ ZJDelete  = ZJDelete
    
type instance (PatchDelta (ZJItem f a)) = ZJPatch f a
type instance (FunctorDelta (ZJItem f)) = ZJPatch f

instance (FDEFunctor f, 
          FDEConstraint f a, 
          Patchable (f a),
          PatchInstance (FunctorDelta f a))
            => PatchInstance (ZJPatch f a) where
    mergepatches (ZJDelta da0) (ZJDelta da1) = ZJDelta (mergepatches da0 da1)
    mergepatches (ZJAdd     a) (ZJDelta da)  = ZJAdd $ patch a (fromFD da)
    mergepatches (ZJDelete)    (ZJDelta da)  = ZJDelete
    -- add and delete just replace whatever came before
    mergepatches _             (ZJAdd da1)   = ZJAdd da1
    mergepatches _             (ZJDelete)    = ZJDelete
    nopatch = ZJDelta nopatch

instance (FDEFunctor f,
          FDEConstraint f a,
          PatchInstance (FunctorDelta f a),
          Patchable (f a))
            => Patchable (ZJItem f a) where
    patch _           (ZJAdd a)    = ZJData a
    patch ZJEmpty     _            = ZJEmpty
    patch (ZJData _)  (ZJAdd a)    = ZJData a
    patch (ZJData _)  ZJDelete     = ZJEmpty
    patch (ZJData a)  (ZJDelta da) = ZJData (patch a (fromFD da))

    changes ZJEmpty     ZJEmpty      = ZJDelta nopatch
    changes ZJEmpty     (ZJData a)   = ZJAdd a
    changes (ZJData a)  ZJEmpty      = ZJDelete
    changes (ZJData a)  (ZJData a')  = ZJDelta $ toFD (changes a a')

instance (FDEFunctor f) => FDECompatible (ZJItem f) where
    type FDEConstraint (ZJItem f) a = 
        (FDECompatible (ZJItem f),
         FDEConstraint f a,
         Patchable (f a),
         PatchInstance (FunctorDelta f a))

    toFDE z = let (v,dv) = zdEval z in FDE v dv
    fromFDE (FDE v dv) = ZDV v dv

    toFD z = z
    fromFD z = z
