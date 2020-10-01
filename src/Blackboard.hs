{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

--

-- | A "Scratch Buffer" used for experimental code.
module Blackboard where

--import Data.Monoid (Sum(..))

import Prelude
--import Control.Category.Constrained.Prelude
--import qualified Control.Category.Hask as Hask

--import Control.Monad.Constrained
--import Control.Arrow.Constrained

import Control.Applicative
import Control.Lens

import Data.Proxy
import Data.Monoid
import Data.Hashable
import Data.Kind
import qualified Data.Map as Map

import Hedgehog
import qualified Hedgehog.Classes as Classes
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import GHC.Generics
import GHC.IO.Encoding (getLocaleEncoding)
import System.IO (hSetEncoding, stderr, stdout, utf8)

import Zorja.Patchable
import Zorja.Primitives
--import Zorja.Collections.MagicTable

--import Zorja.Collections.ZJIntMap
--import Zorja.Collections.Cofree

-- | 'ZapList' is 'ZipList' with a 'Show1' instance so that 'show' works for @Cofree ZapList a@
newtype ZapList a = ZapList [a]
  deriving (Show, Eq)
  deriving (Functor, Show1) via []

instance Foldable ZapList where
  foldMap fm (ZapList as) = foldMap fm as

instance Applicative ZapList where
  pure x = ZapList [x]
  liftA2 f (ZapList a) (ZapList b) = ZapList (zipWith f a b)




insertRM :: (Ord k, Patchable a, ValDeltaBundle a) => 
  k -> a -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
insertRM k v m = 
  let r = (fromMaybeCRM (Map.lookup k m))
  in
    Map.insert k (set replaceableMaybe (Just v) r) m

lookupRM :: (Ord k, Patchable a, ValDeltaBundle a) =>
  k -> Map.Map k (ReplaceableMaybe a) -> Maybe a
lookupRM k m = let (ReplaceableMaybe v) = (fromMaybeCRM (Map.lookup k m))
               in view replaceable v

-- | Modify the post-delta value while leaving the original value unchanged.
--   To change the original AND the delta, use 'Map.alter' with a 
--   @ReplaceableMaybe a -> ReplaceableMaybe a@
adjustRM :: (Ord k, Patchable a, ValDeltaBundle a) =>
  (a -> a) -> k -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
adjustRM f k m = let (ReplaceableMaybe v) = fromMaybeCRM (Map.lookup k m)
                 in Map.insert k (ReplaceableMaybe $ (over replaceable (fmap f) v)) m
             
deleteRM :: (Ord k, ValDeltaBundle a) =>
  k -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
deleteRM k m =
    case (Map.lookup k m) of
        Nothing -> m
        Just (ReplaceableMaybe v) ->
            let v' = case v of
                        (ReplaceableValDelta vd) -> let (a,_) = unbundleVD vd
                                                    in ReplaceableValues a Nothing
                        (ReplaceableValues a _) -> ReplaceableValues a Nothing
            in
              Map.insert k (ReplaceableMaybe v') m

updateRM :: (Ord k, ValDeltaBundle a, Patchable a, Eq a, Eq (ValDelta a)) =>
  (a -> Maybe a) -> k -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
updateRM f k m = alterRM f' k m
    where f' Nothing = Nothing
          f' (Just x) = f x

alterRM :: (Ord k, ValDeltaBundle a, Patchable a, Eq a, Eq (ValDelta a)) =>
  (Maybe a -> Maybe a) -> k -> Map.Map k (ReplaceableMaybe a) -> Map.Map k (ReplaceableMaybe a)
alterRM f k m = Map.alter f' k m
    where f' = toMaybeCRM . (over replaceableMaybe f) . fromMaybeCRM


x1 :: ValDelta (ReplaceOnly String)
x1 = ReplaceValDelta "argh" (Replacing (Just "ack"))

x2 :: ReplaceableValDelta Bool
x2 = ReplaceableValDelta $ BoolVD True

x3 :: [ReplaceableMaybe (DiffNum Integer)]
x3 = (fmap (unfurlVal . DNum) [5,6]) ++   -- numbers that don't change
     [ReplaceableMaybe $ ReplaceableValues (Just (DNum 4)) Nothing] ++    -- represents a deletion
     [ReplaceableMaybe $ ReplaceableValDelta (Just (DValDelta 1 (-4)))] ++ -- a number that changes
     (fmap (unfurlAdd . DNum) [1,2]) -- represents adds

x4 :: Map.Map Integer (ReplaceableMaybe (Thingy 'HKDValue))
x4 = Map.fromList []

x5 :: Bool -> DiffNum Integer
x5 True = DNum 3
x5 False = DNum 4

-- | A transformer for 'DiffNum' that clamps to some value
x6 :: Integer -> ValDelta (DiffNum Integer) -> ValDelta (DiffNum Integer)
x6 clamp = tIf (< (DNum clamp))     -- test
               (const (DNum clamp)) -- then
               (id)             -- else

x7 :: (CollapseReplaceableMaybe a, Monoid (ValDelta a)) => [ReplaceableMaybe a] -> ValDelta a
x7 xs = foldMap collapse xs

data HKDRoute = HKDValue | HKDDelta | HKDValDelta

type family HKD (f :: HKDRoute) a where
  HKD 'HKDValue a = a
  HKD 'HKDDelta a = ILCDelta a
  HKD 'HKDValDelta a = ValDelta a

--
-- a product type
--

data Thingy f = Thingy {
  _position :: HKD f (ReplaceOnly (Double,Double)),
  _name     :: HKD f (ReplaceOnly String),
  _mesh     :: HKD f (ReplaceOnly String)
  } deriving (Generic)

makeLenses ''Thingy

instance (Show (HKD f (ReplaceOnly (Double,Double))),
          Show (HKD f (ReplaceOnly String))
          ) => Show (Thingy f) where
    show (Thingy p n m) = "Thingy (" ++ show p ++ ") (" ++ show n ++ ") (" ++ show m ++ ")"

type instance ILCDelta (Thingy 'HKDValue) = Thingy 'HKDDelta
type instance ValDelta (Thingy 'HKDValue) = Thingy 'HKDValDelta

instance ValDeltaBundle (Thingy 'HKDValue)
instance PatchInstance (Thingy 'HKDDelta)
instance Patchable (Thingy 'HKDValue)



--
-- a sum type
--

data SumThingy f = SumThing (HKD f (ReplaceOnly Integer))
                |  OtherThing (HKD f (ReplaceOnly String))
  deriving (Generic)


type instance ILCDelta (SumThingy 'HKDValue) = SumThingy 'HKDDelta
type instance ValDelta (SumThingy 'HKDValue) = SumThingy 'HKDValDelta

makePrisms ''SumThingy

instance ValDeltaBundle (SumThingy 'HKDValue)
instance PatchInstance (SumThingy 'HKDDelta)
instance Patchable (SumThingy 'HKDValue)


--
-- A 'safe' sum type that can handle switching constructors
--

instance PatchReplaceable (SumThingy 'HKDValue) where
    replaceableChanges (SumThing i)   (SumThing i')   = ReplaceablePatch $ SumThing (changes i i')
    replaceableChanges (SumThing _)   (OtherThing o)  = ReplaceableNew $ OtherThing o
    replaceableChanges (OtherThing _) (SumThing i)    = ReplaceableNew $ SumThing i
    replaceableChanges (OtherThing o) (OtherThing o') = ReplaceablePatch $ OtherThing (changes o o')

    safeBundle ((SumThing x),   (SumThing dx))   = SumThing (bundleVD (x,dx))
    safeBundle ((OtherThing x), (OtherThing dx)) = OtherThing (bundleVD (x,dx))
    safeBundle ((SumThing x),   (OtherThing _))  = SumThing (bundleVD (x,noPatch))
    safeBundle ((OtherThing x), (SumThing _))    = OtherThing (bundleVD (x,noPatch))

    valDeltaNoPatch (SumThing x)   = SumThing (bundleVD (x,noPatch))
    valDeltaNoPatch (OtherThing x) = OtherThing (bundleVD (x,noPatch))

newtype SumThingySafe = SumThingySafe (ReplaceableVal (SumThingy 'HKDValue))
    deriving (Generic)
    deriving (Patchable) via (ReplaceableVal (SumThingy 'HKDValue))
  
newtype SumThingySafeD = SumThingySafeD (ReplaceableDelta (SumThingy 'HKDValue))
    deriving (PatchInstance) via (ReplaceableDelta (SumThingy 'HKDValue))

newtype SumThingySafeVD = SumThingySafeVD (ReplaceableValDelta (SumThingy 'HKDValue))

type instance ILCDelta (SumThingySafe) = SumThingySafeD
type instance ValDelta (SumThingySafe) = SumThingySafeVD


--
-- Thingy functions
--

thingyToKey :: Thingy 'HKDValDelta -> Int
thingyToKey t = let (ReplaceOnly n) = t ^. name . valDelta
                in hash n

mkThingy :: (Double, Double) -> String -> String -> Thingy 'HKDValue
mkThingy p n m = Thingy (ReplaceOnly p) (ReplaceOnly n) (ReplaceOnly m)

{-tableOfStuff :: MagicJetTable (Thingy 'HKDValue)
tableOfStuff = fromList thingyToKey $
  fmap (\x -> bundleVD (x,noPatch)) [
  (mkThingyVal (3.0,2.0) "学生"),
  (mkThingyVal (1.0,1.0) "Bob"),
  (mkThingyVal (4.0,5.0) "Blorpshaft")
  ]-}
xy :: [Char]
xy = "就这?"

newtype MapX i a = MapX (Map.Map i (ReplaceableValDelta (Maybe a)))

mapOfStuff :: Map.Map Int (ReplaceableMaybe (Thingy 'HKDValue))
mapOfStuff = insertRM 3 (mkThingy (3.0,2.0) "bob" "argh") (Map.fromList [])



stepPosition :: (Double,Double) -> (Double,Double)
stepPosition (a,b) = (a,b+0.03)

--y = x ^? _Just .valueLens

-- [ ReplaceableValDelta (valDeltaNoPatch (Just (mkThingyVal (3.0,2.0) "Bob"))) ]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8

--b <- Classes.lawsCheck $ Classes.comonadLaws genTwoVal
--putStrLn $ show b

tests :: IO Bool
tests =
  checkParallel $$(discover)

prop_reverse :: Property
prop_reverse =
  property $ do
    xs <- forAll $ Gen.list (Range.linear 0 100) Gen.alpha
    reverse (reverse xs) === xs


