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

--import Data.Kind (Constraint, Type)

import Control.Lens hiding (from, to)
--import Control.Lens.Tuple
import Control.Monad.State

import Zorja.Patchable
import Zorja.Jet


--
-- A trick to remove Identity in higher-kinded types
--

data HKDDelta a

type family HKD f a where
  HKD Identity a = a
  HKD HKDDelta a = PatchDelta a
  HKD f a        = f a


--
-- Some record. We want to record changes to this record
-- (performed using lenses) incrementally.
--
data SomeDude f = SD
  {
    v1 :: HKD f (ANum Int, ANum Int),
    v2 :: HKD f (Text)
  } deriving (Generic)

type instance PatchDelta (SomeDude Identity) = SomeDude HKDDelta

--
-- default type is SomeDude Identity, the diff type is SomeDude HKDDelta
--

deriving instance Show (SomeDude Identity)
deriving instance Show (SomeDude HKDDelta)


instance Semigroup (SomeDude HKDDelta) where
  (SD f1 f2) <> (SD f1' f2') = SD (f1 <> f1') (f2 <> f2')

instance Monoid (SomeDude HKDDelta) where
  mempty = SD mempty mempty
  mappend = (<>)

instance Patchable (SomeDude Identity) where
  patch s ds = patchGeneric s ds
  changes s1 s2 = changesGeneric s1 s2


--
-- SomeDude rec
-- 


startDudeValue :: SomeDude Identity
startDudeValue = SD {
  v1 = (3,3),
  v2 = (pack "argh")
  }

processDudeValue :: StateT (PatchedJet (SomeDude Identity)) IO ()
processDudeValue = do
  v <- get
  let v1' = getLensFor . v1 $ pjlensfor v
  v1' . _1 .= 4

--  (SD { v1 = Ax 5 3, v2 = (pack "argh")})

main :: IO ()
main = do
  let x = toJet (AtomicLast (3 :: Integer))
  putStrLn $ show x
  putStrLn $ "Initial DudeValue: " ++ show startDudeValue
  dd <- execStateT processDudeValue (toPatchedJet startDudeValue)
  putStrLn $ "DudeValue after process: " ++ show dd
  putStrLn $ "DudeValue change: " ++ show (history dd) --(changes startDudeValue dd)
  


