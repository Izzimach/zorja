{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module TwoVal where

import Zorja.Combine

import Data.Functor.Foldable
import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree

data TwoChoose = ChooseOne | ChooseTwo
    deriving (Eq, Show)

-- | A 2-tuple as a sorta-comonad. This wraps two (possibly different) comonads
data TwoVal w v a = TwoVal TwoChoose (w a) (v a)
    deriving (Eq, Show)

newtype TwoValBase w v a x = TwoValBase (T2ZipCombined (Base (w a)) (Base (v a)) x)

type instance Base (TwoVal w v a) = TwoValBase w v a

-- | choose which value to extract - similar to 'seek' for 'StoreT'
reChoose :: TwoVal w v a -> TwoChoose -> TwoVal w v a
reChoose (TwoVal c wa va) c' = TwoVal c' wa va

-- | Helper function to pick one of the stored values
twoChooser :: (Comonad w, Comonad v) => w a -> v a -> TwoChoose -> a
twoChooser wa va ChooseOne = extract wa
twoChooser wa va ChooseTwo = extract va

twoZip :: (T2Zip w v) => TwoVal w v a -> T2Zipped w v a
twoZip (TwoVal c wa va) = t2Zip (wa, va)

twoUnzip :: (T2Zip w v) => T2Zipped w v a -> TwoVal w v a
twoUnzip cz = let (wa,va) = t2Unzip cz
              in TwoVal ChooseOne wa va

runTwo :: TwoVal w v a -> (TwoChoose, w a, v a)
runTwo (TwoVal c wa va) = (c, wa, va)


--
-- Typeclass instances for TwoVal
--

instance (Functor w, Functor v) => Functor (TwoVal w v) where
    fmap f (TwoVal c t1 t2) = TwoVal c (fmap f t1) (fmap f t2)

instance (Comonad w, Comonad v) => Comonad (TwoVal w v) where
    extract (TwoVal ChooseOne wa _va) = extract wa
    extract (TwoVal ChooseTwo _wa va) = extract va
    extend f (TwoVal c wa va) = TwoVal c (extendW wa) (extendV va)
        where
            extendW = extend (\wa' -> f (TwoVal ChooseOne wa' va))
            extendV = extend (\va' -> f (TwoVal ChooseTwo wa va'))
    duplicate (TwoVal c wa va) = TwoVal c (dupW wa) (dupV va)
        where
            dupW = extend (\wa' -> TwoVal ChooseOne wa' va)
            dupV = extend (\va' -> TwoVal ChooseTwo wa  va')

instance (Functor (T2ZipCombined (Base (w a)) (Base (v a)))) => Functor (TwoValBase w v a) where
    fmap f (TwoValBase x) = TwoValBase (fmap f x)

instance (Recursive (w a),
          Recursive (v a), 
          T2ZipCombine (Base (w a)) (Base (v a)), 
          T2Combine (w a) (v a),
          Functor (T2ZipCombined (Base (w a)) (Base (v a)))) => Recursive (TwoVal w v a) where
    project (TwoVal c wa va) = let wax = project wa
                                   vax = project va
                                   wvax = t2ZipCombine (wax,vax)
                               in TwoValBase (fmap twoSunder wvax)
        where
            twoSunder :: (T2Combine (w a) (v a)) => T2Combined (w a) (v a) -> TwoVal w v a
            twoSunder x = let (a,b) = t2Sunder x
                          in TwoVal ChooseOne a b

instance (T2ZipCombine (Base (w a)) (Base (v a)),
          Corecursive (w a),
          Corecursive (v a),
          T2Combine (w a) (v a),
          Functor (T2ZipCombined (Base (w a)) (Base (v a)))) => Corecursive (TwoVal w v a) where
    embed (TwoValBase x) = let fx = fmap twoCombine x
                               (a,b) = t2UnzipSunder fx
                           in TwoVal ChooseOne (embed a) (embed b)
        where
            twoCombine :: (T2Combine (w a) (v a)) => TwoVal w v a -> T2Combined (w a) (v a)
            twoCombine (TwoVal c wa va) = t2Combine (wa,va)

instance (Applicative f) => ComonadCofree f (TwoVal (Cofree f) (Cofree f)) where
    unwrap (TwoVal c wa va) = liftA2 (TwoVal c) (unwrap wa) (unwrap va)


