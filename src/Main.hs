{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import GHC.Generics

import Data.Text as T
--import Data.Semigroup hiding (diff, All)
import Data.Monoid (Sum(..))

import Data.Kind (Constraint, Type)

import Control.Lens hiding (from, to)
--import Control.Lens.Tuple
import Control.Monad.State

import Zorja.Patchable
import Zorja.Jet
import Zorja.Collections.PatchableSet (PatchableSet)
import Zorja.ZHOAS
import qualified Zorja.Collections.PatchableSet as S


--
-- A trick to remove Identity in higher-kinded types
--

data HKDDelta a

type family HKD f a where
    HKD Identity a = a
    HKD HKDDelta a = PatchDelta a
    HKD f a        = f a

--
--
--


--
-- Some record. We want to record changes to this record
-- (performed using lenses) incrementally.
--
data SomeDude f = SD
  {
    v1 :: HKD f (ANum Int, ANum Int)
  , v2 :: HKD f (Text)
  , v3 :: HKD f (PatchableSet Int)
  } deriving (Generic)

type instance PatchDelta (SomeDude Identity) = SomeDude HKDDelta


class PJLensible z where
    getPJLenses :: z (PJLensFor (z Identity))

instance PJLensible SomeDude where
    getPJLenses = SD 
                {
                  v1 = PJLensFor $ \l pj -> 
                      let val = (patchedval) pj
                          hist = (history) pj
                          v1val' = l (PatchedJet (v1 val) (v1 hist))
                          rebuild = \val' -> PatchedJet {
                            patchedval = val { v1 = patchedval val' },
                            history    = hist { v1 = history val'}
                          }
                      in fmap rebuild v1val'
                  ,
                  v2 = PJLensFor $ \l pj -> 
                      let val = (patchedval) pj
                          hist = (history) pj
                          v1val' = l (PatchedJet (v2 val) (v2 hist))
                          rebuild = \val' -> PatchedJet {
                            patchedval = val { v2 = patchedval val' },
                            history    = hist { v2 = history val'}
                          }
                      in fmap rebuild v1val'
                  ,
                  v3 = PJLensFor $ \l pj -> 
                    let val = (patchedval) pj
                        hist = (history) pj
                        v3val' = l (PatchedJet (v3 val) (v3 hist))
                        rebuild = \val' -> PatchedJet {
                          patchedval = val { v3 = patchedval val' },
                          history    = hist { v3 = history val'}
                        }
                    in fmap rebuild v3val'
                }

--
-- default type is SomeDude Identity, the diff type is SomeDude HKDDelta
--

deriving instance Show (SomeDude Identity)
deriving instance Show (SomeDude HKDDelta)


instance Semigroup (SomeDude HKDDelta) where
    (SD f1 f2 f3) <> (SD f1' f2' f3') = SD (f1 <> f1') (f2 <> f2') (f3 <> f3')

instance Monoid (SomeDude HKDDelta) where
    mempty = SD mempty mempty mempty

instance Patchable (SomeDude Identity) where
    patch s ds = patchGeneric s ds
    changes s1 s2 = changesGeneric s1 s2

--
-- lens to adapt (.=) to PatchedJet values
--
-- example, for a (PatchedJet (Int, Int)) instead of:
-- _1 .= 3
-- use:
-- _1 . difP  .= 3
--
difP :: (Patchable z) => Lens' (PatchedJet z) z
difP l = \pj -> let v = (patchedval pj)
                    h = history pj
                    rebuild = \v' ->
                        PatchedJet v' (h <> (changes v v'))
                in fmap rebuild (l v)

--(.=) :: (MonadState s m) => ASetter s s a b -> b -> m ()
--l .= b = modify ((l . difP) .~ b)
--infixr 4 .=

--
-- SomeDude rec
-- 

startDudeValue :: SomeDude Identity
startDudeValue = SD {
    v1 = (3,3)
  , v2 = (pack "argh")
  , v3 = S.empty
  }

processDudeValue :: StateT (PatchedJet (SomeDude Identity)) IO ()
processDudeValue = do
    let SD (PJLensFor v1') (PJLensFor v2') (PJLensFor v3') = getPJLenses
    v1' . _1 . difP .= (ANum (4 :: Int))
    v2'      . difP .= (pack "blargh")
    v3'             %= S.insert 4
    v3'             %= S.insert 7
    v3'             %= S.delete 4

--
-- test of sum type using integers
--

newtype SomeNum = SomeNum { getSomeNum :: Integer }

type instance (PatchDelta SomeNum) = Sum Integer

instance (Patchable SomeNum) where
  patch (SomeNum a) (Sum da) = SomeNum (a + da)
  changes (SomeNum a) (SomeNum b) = Sum (b - a)

--
-- a Simple patchable sum type
--
data BiggerSmaller = Bigger | Smaller deriving (Eq, Show)
data PatchSumType a = Value a | PatchSum a | NoPatch deriving (Eq, Show)

type instance (PatchDelta BiggerSmaller) = PatchSumType BiggerSmaller

instance Semigroup (PatchSumType a) where
    a <> NoPatch = a
    _ <> b = b
    
instance Monoid (PatchSumType a) where
    mempty = NoPatch

instance Patchable (BiggerSmaller) where
    patch a da = case da of
                     PatchSum b -> b
                     Value b -> b
                     NoPatch -> a
    changes _a b = Value b


ifBigger :: ANum Integer -> BiggerSmaller
ifBigger (ANum x) = if x > 8 then Bigger else Smaller


testProcessDudeValue = do
    putStrLn $ "Initial DudeValue: " ++ show startDudeValue
    dd <- execStateT processDudeValue (toPatchedJet startDudeValue)
    putStrLn $ "DudeValue after process: " ++ show (patchedval dd)
    putStrLn $ "DudeValue change: "        ++ show (history dd) --(changes startDudeValue dd)

testZHOAS = do
    let fork = (zLiftIf 
                    (\a -> ZBool $ a > 8) 
                    (ZDV Bigger mempty)
                    (ZDV Smaller mempty))
    let v  = ANum (6 :: Integer)
    let v' = ANum (9 :: Integer)
    let dv = changes v v'
    let (b,db) = zdEval $ fork `app` (ZDV v dv)
    putStrLn  $ "v: " ++ show v ++ "     b: "++ show b
    putStrLn $ "dv: " ++ show dv ++ "     db: " ++ show db
    let b' = patch b db
    putStrLn $ "v': " ++ show v' ++ "     b': " ++ show b'


main :: IO ()
main = do
    let x = toJet (AtomicLast (3 :: Integer))
    putStrLn $ show x

    testProcessDudeValue

