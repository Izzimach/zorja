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

module Zorja.Collections.Spliceable where

import Zorja.Patchable
import Zorja.ZHOAS

import Data.Monoid
import Data.Functor.Foldable
import Data.Proxy

import qualified Data.Text as T

import qualified Data.Vector as V
import qualified Data.Vector.Distance as VD

--
-- | a splice action has a (start,end) range and the new value
-- | to replace what was in that range. The length of the
-- | new data may not be (end-start) in which case
-- | the splice result will have a different length.
--

data SpliceAction a = SPLS
    {
        start :: Integer,
        length :: Integer,
        newChunk :: a
    }
    deriving (Eq, Show)

mkSplice :: Integer -> Integer -> a -> SpliceAction a
mkSplice s l n = SPLS s l n

type SpliceList a = [SpliceAction a]


class SpliceArray a where
    deltaToSplice :: PatchDelta a -> SpliceList a
    spliceToDelta :: SpliceList a -> PatchDelta a
    chunkSize :: a -> Integer
    spliceInChunk :: a -> SpliceAction a -> a

shiftSplice :: Integer -> SpliceAction a -> SpliceAction a
shiftSplice offset (SPLS s l n) = SPLS (s + offset) l n

concatSpliceDExpr :: forall a. (Patchable a, SpliceArray a, Semigroup a) => ZDExpr a -> ZDExpr a -> ZDExpr a
concatSpliceDExpr l r =
    let (tl,dtl) = zdEval l
        (tr,dtr) = zdEval r
        -- convert deltas to splice lists
        p = Proxy :: Proxy a
        spll = deltaToSplice @a dtl
        splr = deltaToSplice @a dtr
        leftoffset = chunkSize tl
        -- adjust offsets of the right splice to take into account
        -- the offset of the left chunk
        adjsplr = fmap (shiftSplice (toInteger leftoffset)) splr
    -- if we apply the left splices first, than the length of the
    -- left chunk will change and the right splices will be wrong,
    -- so instead we apply the right splices first which won't
    -- effect the left splices
    in ZDV (tl <> tr) (spliceToDelta @a (adjsplr <> spll))


--
-- | SpliceArray instance for Text
--
instance SpliceArray T.Text where
    deltaToSplice a = a
    spliceToDelta a = a
    chunkSize a = toInteger $ T.length a
    spliceInChunk orig (SPLS s l n) =
        let prefix = T.take (fromInteger s)       orig
            suffix = T.drop (fromInteger (s + l)) orig
        in T.concat [prefix, n, suffix]

type instance PatchDelta T.Text = SpliceList T.Text

instance Patchable T.Text where
    patch a da = foldl spliceInChunk a da
    changes a a' = -- punt for now, just replace it all
        [SPLS 0 (chunkSize a) a']
        
--
-- | SpliceArray instance for Data.Vector
-- |
-- | Note that we don't require @Patchable a@ since elements are not patched,
-- | they are just straight up replaced when splicing. An alternate version might support
-- | deltas on specific elements.
--
instance SpliceArray (V.Vector a) where
    deltaToSplice a = a
    spliceToDelta a = a
    chunkSize a = toInteger $ V.length a
    spliceInChunk orig (SPLS s l n) =
        let prefix = V.take (fromInteger s)       orig
            suffix = V.drop (fromInteger (s + l)) orig
        in V.concat [prefix, n, suffix]

type instance PatchDelta (V.Vector a) = SpliceList (V.Vector a)

instance (Eq a) => Patchable (V.Vector a) where
    patch a da = foldl spliceInChunk a da
    changes a a' = [SPLS 0 (chunkSize a) a'] -- not effiecient but technically correct


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

