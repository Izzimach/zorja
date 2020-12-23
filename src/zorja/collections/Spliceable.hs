{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Zorja.Collections.Tombstone
-- Description : Delta-tracking list using tombstones.
-- Copyright   : (c) Gary Haussmann, 2020
-- Stability   : experimental
--
-- Tracks changes in a list by adding add/remove markers to the list.
module Zorja.Collections.Spliceable
  ( SplicedList (..),
    SplicedListDelta (..),
    SplicedListValDelta (..),
    SpliceElement (..),
    modifyElements,
    head,
    tail,
    take,
    drop,
    filter,
    filterT,
    insertAt,
    cons,
    length
  )
where

import Prelude hiding (head, tail, take, drop, filter, length)

import Data.Maybe

import GHC.Generics
import Zorja.Patchable

--
-- SpliceElement
--

-- | Data for a single spliceable element. We need to hold a marked if the element is
--   being inserted in the delta.
data SpliceElement a = ToAdd | SpliceElement a
  deriving (Eq, Show, Generic)

data SpliceElementDelta a = Deleted a | Added a | SplicePatch (ILCDelta a)
  deriving (Generic)

data SpliceElementValDelta a
  = SpliceAdd a
  | SpliceDelete a
  | SpliceValDelta (ValDelta a)
  deriving (Generic)

instance (Show a, Show (ILCDelta a)) => Show (SpliceElementDelta a) where
  show (Deleted a) = "Deleted " ++ show a
  show (Added a) = "Added " ++ show a
  show (SplicePatch da) = "SplicePatch " ++ show da

instance (Show a, Show (ValDelta a)) => Show (SpliceElementValDelta a) where
  show (SpliceAdd a) = "SpliceAdd " ++ show a
  show (SpliceDelete a) = "SpliceDelete " ++ show a
  show (SpliceValDelta aa) = "SpliceValDelta " ++ show aa

-- take the current element ValDelta and convert it into a delete
deleteElement :: (ValDeltaBundle a) => SpliceElementValDelta a -> Maybe (SpliceElementValDelta a)
deleteElement (SpliceAdd _) = Nothing
deleteElement (SpliceDelete a) = Just $ SpliceDelete a
deleteElement (SpliceValDelta aa) = let (a,_) = unbundleVD aa
                                    in Just $ SpliceDelete a

type instance ILCDelta (SpliceElement a) = SpliceElementDelta a

type instance ValDelta (SpliceElement a) = SpliceElementValDelta a

instance (ValDeltaBundle a) => ValDeltaBundle (SpliceElement a) where
  bundleVD (ToAdd, (Added a)) = SpliceAdd a
  bundleVD ((SpliceElement a), Deleted _) = SpliceDelete a
  bundleVD ((SpliceElement a), (SplicePatch da)) = SpliceValDelta (bundleVD (a, da))
  bundleVD _ = error "Mismatch in SpliceElement bundleVD"

  unbundleVD (SpliceAdd a) = (ToAdd, Added a)
  unbundleVD (SpliceDelete a) = (SpliceElement a, Deleted a)
  unbundleVD (SpliceValDelta va) =
    let (a, da) = unbundleVD va
     in (SpliceElement a, SplicePatch da)

  valueBundle ToAdd = error "Can't valueBundle ToAdd"
  valueBundle (SpliceElement a) = SpliceValDelta (valueBundle a)


instance (Patchable a) => Patchable (SpliceElement a) where
    patch (SpliceAdd a) = SpliceElement a
    patch (SpliceDelete _) = ToAdd
    patch (SpliceValDelta va) = SpliceElement (patch va)

    changes ToAdd             ToAdd              = error "Changes of missing elements"
    changes ToAdd             (SpliceElement a') = Added a'
    changes (SpliceElement a) (SpliceElement a') = SplicePatch (changes a a')
    changes (SpliceElement a) ToAdd              = Deleted a

    diffBundle ToAdd             ToAdd              = error "Cannot diff two ToAdd values"
    diffBundle ToAdd             (SpliceElement a') = SpliceAdd a'
    diffBundle (SpliceElement a) ToAdd              = SpliceDelete a
    diffBundle (SpliceElement a) (SpliceElement a') = SpliceValDelta (diffBundle a a')


instance (Patchable a) => PatchInstance (SpliceElementDelta a) where
  _           <^< Deleted a        = Deleted a
  (Deleted a) <^< (Added a')       = SplicePatch (changes a a')
  (Added a)   <^< (SplicePatch da) = Added (patch $ bundleVD (a, da))
  (SplicePatch da) <^< (SplicePatch da') = SplicePatch (da <^< da')
  _ <^< _ = error "Mismatch in SpliceElement (<^<)"

--
-- SplicedList
--

-- | For a list the delta is a list of 'SpliceElement'.
--   If the delta is shorter than the original, missing elements are
--   no-ops: @SpliceElement [] Buried@.
--   Also the delta can be one element longer than the original value if
--   elements are appended to the end.
newtype SplicedList a = SplicedList [a]
  deriving (Eq, Show, Generic)

newtype SplicedListDelta a = SplicedListDelta [SpliceElementDelta a]
  deriving (Generic)

newtype SplicedListValDelta a = SplicedListValDelta [SpliceElementValDelta a]
  deriving (Generic)

type instance ILCDelta (SplicedList a) = SplicedListDelta a

type instance ValDelta (SplicedList a) = SplicedListValDelta a

instance (Show a, Show (ILCDelta a)) => Show (SplicedListDelta a) where
  show (SplicedListDelta as) = "SplicedListDelta " ++ show as

instance (Show a, Show (ValDelta a)) => Show (SplicedListValDelta a) where
  show (SplicedListValDelta as) = "SplicedListValDelta " ++ show as

-- | Remove tombstone markers from a list of SpliceElements
unSplice :: [SpliceElement a] -> SplicedList a
unSplice [] = SplicedList []
unSplice (ToAdd : xs) = unSplice xs
unSplice (SpliceElement a : xs) =
  let (SplicedList xs') = unSplice xs
  in SplicedList (a : xs')

-- | An 'fmap' type of operation, with the 'Valdelta' baked in.
modifyElements :: (Patchable a) => (ValDelta a -> ValDelta a) -> SplicedListValDelta a -> SplicedListValDelta a
modifyElements f (SplicedListValDelta as) = SplicedListValDelta $ splice as
  where
    splice []                        = []
    splice ((SpliceAdd x)      : xs) = (SpliceAdd $ patch $ f $ valueBundle x) : xs
    splice ((SpliceDelete x)   : xs) = (SpliceDelete x) : xs
    splice ((SpliceValDelta x) : xs) = (SpliceValDelta (f x)) : xs

instance (ValDeltaBundle a) => ValDeltaBundle (SplicedList a) where
  bundleVD (SplicedList a, SplicedListDelta da) = SplicedListValDelta (toSplice a da)
    where
      toSplice [] []                     = []
      toSplice _  []                     = error "Mismatch in bundle for SplicedList"
      toSplice xs (Added x : dxs)        = (SpliceAdd x) : (toSplice xs dxs)
      toSplice [] (Deleted _ : _)        = error "Mismatch in bundle for SplicedList"
      toSplice [] (SplicePatch _ : _)    = error "Mismatch in bundle for SplicedList"
      toSplice (x:xs) (Deleted _ : dxs)  = (SpliceDelete x) : (toSplice xs dxs)
      toSplice (x:xs) (SplicePatch dx : dxs) = (SpliceValDelta (bundleVD (x,dx))) : (toSplice xs dxs)
  unbundleVD (SplicedListValDelta vs) =
    let (a, da) = unzip $ map unbundleVD vs
     in (unSplice a, SplicedListDelta da)
  valueBundle (SplicedList a) = SplicedListValDelta (fmap (valueBundle . SpliceElement) a)

instance (Patchable a) => Patchable (SplicedList a) where
  patch (SplicedListValDelta vs) = unSplice (fmap patch vs)

  -- For changes we diff element-mise and use Add/Delete to fixup any difference in length
  changes (SplicedList a) (SplicedList a') = SplicedListDelta (changesRaw a a')
    where
      changesRaw (x:xs) (y:ys) = (SplicePatch $ changes x y) : changesRaw xs ys
      changesRaw []     ys     = fmap Added ys
      changesRaw xs     []     = fmap Deleted xs


  diffBundle (SplicedList a) (SplicedList a') = SplicedListValDelta (changesRaw a a')
    where
      changesRaw (x:xs) (y:ys) = (SpliceValDelta $ diffBundle x y) : changesRaw xs ys
      changesRaw []     ys     = fmap SpliceAdd ys
      changesRaw xs     []     = fmap SpliceDelete xs


instance (Patchable a) => PatchInstance (SplicedListDelta a) where
  (SplicedListDelta a) <^< (SplicedListDelta b) = SplicedListDelta $ mergeRaw a b
     where
       mergeRaw []               [] = []
       
       -- if the first patch is longer, it's because there were deletes at the end
       mergeRaw (Deleted x : xs) ys = (Deleted x) : mergeRaw xs ys
       mergeRaw _                [] = error "Merge mismatch for SplicedListDelta"

       -- if the second patch is longer it's because there were adds at the end
       -- also an add didn't have an entry in the previous patch so don't consume
       -- the elements in xs
       mergeRaw xs (Added y :ys) = (Added y) : mergeRaw xs ys
       mergeRaw [] _             = error "Merge mismatch for SplicedListDelta"

       -- an add followed by a delete totally vanishes
       mergeRaw (Added _:xs) (Deleted _ : ys) = mergeRaw xs ys

       -- special cases handled, just merge the elements now
       mergeRaw (x:xs) (y:ys)    = (x <^< y) : mergeRaw xs ys



head :: (Patchable a) => SplicedListValDelta a -> Maybe (ValDelta a)
head (SplicedListValDelta []) = Nothing
head (SplicedListValDelta (SpliceAdd x : _)) = Just (valueBundle x)
-- if the head was deleted, try the next element
head (SplicedListValDelta (SpliceDelete _ : xs)) = head (SplicedListValDelta xs)
head (SplicedListValDelta (SpliceValDelta vx : _)) = Just vx

tail :: (Patchable a) => SplicedListValDelta a -> SplicedListValDelta a
tail (SplicedListValDelta []) = SplicedListValDelta []
tail (SplicedListValDelta (x:xs)) =
    case x of
        -- usually we convert the first element to 'SpliceDelete' to indicate it was thrown away
        (SpliceAdd v)       -> SplicedListValDelta (SpliceDelete v                  : xs)
        (SpliceValDelta vv) -> SplicedListValDelta (SpliceDelete (valueUnbundle vv) : xs)
        -- if the head was ALREADY deleted, skip it and try to run tail on the rest of the list
        (SpliceDelete v)    -> 
            let SplicedListValDelta xs' = tail (SplicedListValDelta xs)
            in  SplicedListValDelta (SpliceDelete v : xs')

take :: (Patchable a) => Int -> SplicedListValDelta a -> SplicedListValDelta a
take n (SplicedListValDelta as) =
  if (n <= 0)
  -- delete the rest of the elements
  then SplicedListValDelta (mapMaybe deleteElement as)
  else case as of
    []                    -> SplicedListValDelta []
    (SpliceDelete v) : xs ->
        let SplicedListValDelta xs' = take n (SplicedListValDelta xs)
        in  SplicedListValDelta ((SpliceDelete v) : xs')
    x : xs                ->
        let SplicedListValDelta xs' = take (n-1) (SplicedListValDelta xs)
        in  SplicedListValDelta (x:xs')
        

drop :: (Patchable a) => Int -> SplicedListValDelta a -> SplicedListValDelta a
drop n a@(SplicedListValDelta as) =
  if (n <= 0)
  then a
  else case as of
      []                       -> a
      -- this element was added, so deleting completely removes it with no tombstone
      (SpliceAdd _) : xs       -> drop (n-1) (SplicedListValDelta xs)
      -- this element was already deleted, so skip over it
      (SpliceDelete v) : xs    ->
          let SplicedListValDelta xs' = drop n (SplicedListValDelta xs)
          in  SplicedListValDelta ((SpliceDelete v) : xs')
      -- delete this value (remembering the original pre-patch value) and leave a tombstone
      (SpliceValDelta vv) : xs ->
          let SplicedListValDelta xs' = drop (n-1) (SplicedListValDelta xs)
              (v,_) = unbundleVD vv
          in  SplicedListValDelta ((SpliceDelete v) : xs')

-- | Update style filter - updates the patch to keep only elements that satisfy the predicate
filter :: (Patchable a) => (a -> Bool) -> SplicedListValDelta a -> SplicedListValDelta a
filter f (SplicedListValDelta as) = SplicedListValDelta (filterRaw f as)
  where
    filterRaw _ []                         = []
    filterRaw p (x@(SpliceAdd a) : xs)     = if (p a)
                                             then x : filterRaw p xs
                                             else filterRaw p xs
    filterRaw p (x@(SpliceDelete _) : xs)    = x : filterRaw p xs
    filterRaw p (x@(SpliceValDelta aa) : xs) = if (p (patch aa))
                                             then x : filterRaw p xs
                                             else let (a,_) = unbundleVD aa
                                                  in (SpliceDelete a) : filterRaw p xs
  

-- | Transform filter - keeps elements based on some predicate, without worrying about
--   pre- or post- patch value
filterT :: (Patchable a) => (a -> Bool) -> SplicedListValDelta a -> SplicedListValDelta a
filterT p (SplicedListValDelta as) = SplicedListValDelta (filterTRaw p as)
    where
      filterTRaw _ [] = []
      filterTRaw f (x : xs) =
          let xs' = filterTRaw f xs
          in case x of
               (SpliceAdd a)       -> if (f a) then (x:xs') else xs'
               (SpliceDelete a)    -> if (f a) then (x:xs') else xs'
               (SpliceValDelta aa) ->
                    let (a,_) = unbundleVD aa
                        a'    = patch aa
                    in case (f a, f a') of
                         (True,True)   -> x : xs'
                         (True,False)  -> (SpliceDelete a) : xs'
                         (False, True) -> (SpliceAdd a) : xs'
                         (False, False) -> xs'

insertAt :: Int -> a -> SplicedListValDelta a -> SplicedListValDelta a
insertAt n' a' (SplicedListValDelta as') = SplicedListValDelta $ insertAtRaw n' a' as'
  where
    insertAtRaw n v as =
      if n <= 0
      then ((SpliceAdd v) : as)
      else case as of
         -- no more left, just insert at the end
         []                   -> [SpliceAdd v]
         -- if deleted it doesn't count
         (SpliceDelete x): xs -> (SpliceDelete x) : (insertAtRaw n v xs)
         (x:xs)               -> x : (insertAtRaw (n-1) v xs)

cons :: a -> SplicedListValDelta a -> SplicedListValDelta a
cons v (SplicedListValDelta as) = SplicedListValDelta ((SpliceAdd v) : as)

length :: SplicedListValDelta a -> Int
length (SplicedListValDelta as) = lengthRaw as
  where
    lengthRaw [] = 0
    -- deleted elements don't count toward the length
    lengthRaw (SpliceDelete _ : xs) = lengthRaw xs
    lengthRaw (_ : xs) = 1 + lengthRaw xs
