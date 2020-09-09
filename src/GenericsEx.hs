{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module GenericsEx where

import Control.Monad.Writer
import Data.Kind (Type)
import Data.Text (Text, pack)
import Data.Typeable
import Data.Vector (fromList)

import GHC.Generics
import GHC.TypeLits
import qualified GHC.TypeLits as Err


class GEq a where
  geq :: a x -> a x -> Bool

instance GEq U1 where
  geq U1 U1 = True

instance GEq V1 where
  geq _ _ = True

instance Eq a => GEq (K1 _1 a) where
  geq (K1 a) (K1 b)  =    a == b

instance (GEq a, GEq b) => GEq (a :+: b) where
  geq (L1 a1) (L1 a2) = geq a1 a2
  geq (R1 b1) (R1 b2) = geq b1 b2
  geq _       _       = False

instance (GEq a, GEq b) => GEq (a :*: b) where
  geq (a1 :*: b1) (a2 :*: b2) = geq a1 a2 && geq b1 b2

instance GEq a => GEq (M1 _x _y a) where
  geq (M1 a1) (M1 a2) = geq a1 a2

genericEq :: (Generic a, GEq (Rep a)) => a -> a -> Bool
genericEq a b = geq (from a) (from b)


class ExNihilo a where
  oneCons :: Maybe (a x)

instance ExNihilo U1 where
  oneCons = Just U1

instance ExNihilo (K1 _1 a) where
  oneCons = Nothing

instance ExNihilo (a :*: b) where
  oneCons = Nothing


instance ExNihilo (a :+: b) where
  oneCons  = Nothing

instance (ExNihilo a) => ExNihilo (M1 _x _y a) where
  oneCons = fmap M1 oneCons


exNihilo :: forall a. (Generic a, ExNihilo (Rep a)) => Maybe a
exNihilo = case (oneCons :: Maybe ((Rep a) x)) of
             Nothing    -> Nothing
             v@(Just _) -> fmap to v


data OneC = Argh deriving (Generic, Show, Eq)


