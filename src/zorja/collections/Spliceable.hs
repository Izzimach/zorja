{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGe FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGe TypeFamilies #-}

{-|
Module      : Zorja.Collections.Spliceable
Description : Handle datatypes that can be updated by splicing.
Copyright   : (c) Gary Haussmann, 2019
Stability   : experimental

Spliceable datatypes are things like arrays or strings that support updates via
splicing.  New values are spliced in by specifying a range indexing into the datatype
and the new value to splice into that range.

-}

module Zorja.Collections.Spliceable
    (
        SplicedList(..),
        Splices(..),
        SplicedListVD(..),
        applySplice,
        rmToSplice
    ) where

import GHC.Generics

import Zorja.Patchable
import Zorja.Primitives

import Data.Monoid
import Data.Functor.Foldable
import Data.Proxy

import qualified Data.Text as T

import qualified Data.Vector as V

newtype SplicedList a = SplicedList [a]
    deriving (Eq, Show, Generic)

data Splices a =
      SpliceBranch Int (Splices a) (Splices a)
    | Insert Int [a]
    | Delete Int
    | Skip Int
    | Replace Int [a]

spliceSize :: Splices a -> Int
spliceSize (SpliceBranch i _ _) = i
spliceSize (Insert i _) = i
spliceSize (Delete i)   = i
spliceSize (Skip i) = i
spliceSize (Replace i _) = i

data SplicedListVD a = SplicedListVD [a] (Splices a)

type instance ILCDelta (SplicedList a) = Splices a
type instance ValDelta (SplicedList a) = SplicedListVD a

instance Semigroup (Splices a) where
    (Insert i0 as)  <> (Insert i1 bs)  = Insert (i0+i1) (as ++ bs)
    (Delete i0)     <> (Delete i1)     = Delete (i0+i1)
    (Skip i0)       <> (Skip i1)       = Skip (i0+i1)
    (Replace i0 as) <> (Replace i1 bs) = Replace (i0+i1) (as ++ bs)
    x               <> y               = SpliceBranch (spliceSize x + spliceSize y) x y

instance Monoid (Splices a) where
    mempty = Skip 0
                                       
instance Semigroup (SplicedListVD a) where
    (SplicedListVD a da) <> (SplicedListVD b db) = SplicedListVD (a <> b) (da <> db)

instance Monoid (SplicedListVD a) where
    mempty = SplicedListVD mempty mempty

instance ValDeltaBundle (SplicedList a) where
    bundleVD (SplicedList a, da) = SplicedListVD a da
    unbundleVD (SplicedListVD a da) = (SplicedList a, da)

applySplice :: SplicedListVD a -> [a]
applySplice (SplicedListVD a da) = applySplice' a da

applySplice' :: [a] -> Splices a -> [a]
applySplice' a da =
    case da of
        (SpliceBranch s l r) -> let ls = spliceSize l
                                    la = take ls a
                                    rb = drop ls a
                                in (applySplice' la l) ++ (applySplice' rb r)
        (Insert s as)        -> as ++ a
        (Delete s)           -> []
        (Skip s)             -> a
        (Replace s as)       -> as

-- | Converts a 'ReplaceableMaybe' to a 'SplicedListVD' value. Since 'SplicedListVD' is a 'Monoid'
--   this is useful for folding up things into a list. Since you can't fold up 'ReplaceableMaybe'
--   you instead convert it to 'SplicedListVD' and fold that up, for example @foldMap rmToSplice mapOfRMs@
rmToSplice :: (Patchable a, Eq (ILCDelta a), ValDeltaBundle a) => ReplaceableMaybe a -> SplicedListVD a
rmToSplice (ReplaceableMaybe x) =
    case x of
        ReplaceableValDelta Nothing -> SplicedListVD [] (Skip 0)
        ReplaceableValDelta (Just vd) -> let (a,da) = unbundleVD vd
                                             da' = if (da == noPatch)
                                                   then (Skip 1)
                                                   else (Replace 1 [(patch a da)])
                                         in SplicedListVD [a] da'
        ReplaceableValues Nothing (Just a') -> SplicedListVD [] (Insert 1 [a'])
        ReplaceableValues (Just a) Nothing  -> SplicedListVD [a] (Delete 1)
        ReplaceableValues Nothing Nothing   -> SplicedListVD [] (Skip 0)
        ReplaceableValues (Just a) (Just a') -> SplicedListVD [a] (Replace 1 [a'])
