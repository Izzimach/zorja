{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Zorja.Primitives where

import Data.Semigroup
import Data.Text
import Data.Monoid hiding (Last)

import Zorja.Patchable

newtype AtomicInt = AtomicInt Int deriving (Eq, Show)

instance Patchable AtomicInt where
  type Change AtomicInt = Option (Last AtomicInt)
  patch a da = case getOption da of
                 Nothing -> a
                 Just (Last a') -> a'
  changes a b = if (a == b)
                then Option Nothing
                else Option $ Just (Last b)

instance Num AtomicInt where
  (AtomicInt a) + (AtomicInt b) = AtomicInt (a+b)
  (AtomicInt a) * (AtomicInt b) = AtomicInt (a*b)
  abs (AtomicInt a)             = AtomicInt (abs a)
  signum (AtomicInt a)          = AtomicInt (signum a)
  negate (AtomicInt a)          = AtomicInt (negate a)
  fromInteger a                 = AtomicInt (fromInteger a)





newtype AtomicText = AtomicText Text deriving (Eq, Show)

patchedJetAsText :: PatchedJet AtomicText -> (Text -> Text) -> PatchedJet AtomicText
patchedJetAsText pj f = let (AtomicText oldtext) = patchedval pj
                            oldhistory = history pj
                            newtext = AtomicText $ f oldtext
                            newhistory = oldhistory <> Option (Just (Last newtext))
                        in PatchedJet newtext newhistory
                            

  
instance Semigroup AtomicText where
  (AtomicText a) <> (AtomicText b) = AtomicText (a <> b)

instance Monoid AtomicText where
  mempty = AtomicText mempty
  mappend (AtomicText a) (AtomicText b) = AtomicText (mappend a b)

instance Patchable AtomicText where
  type Change AtomicText = Option (Last AtomicText)
  patch a da = case getOption da of
                 Nothing -> a
                 Just (Last a') -> a'
  changes a b = if (a == b)
                then Option Nothing
                else Option (Just (Last b))
