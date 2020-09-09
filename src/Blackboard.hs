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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

--

-- | A "Scratch Buffer" used for experimental code.
module Blackboard where

--import Data.Monoid (Sum(..))

import Prelude ()
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

import Control.Monad.Constrained

--import Control.Applicative
import Control.Lens

import Data.Hashable
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

--
-- recursive deltas
--
{-
zdAdd :: ZDExpr (DiffNum Integer -> DiffNum Integer -> DiffNum Integer)
zdAdd = lam $ \za ->
            lam $ \zb ->
                let (a,da) = zdEval za
                    (b,db) = zdEval zb
                in
                    ZDV (a + b) (da + db)

zDownFixable :: ZDExpr (DiffNum Integer -> DiffNum Integer) -> ZDExpr (DiffNum Integer -> DiffNum Integer)
zDownFixable zf = lam $ \zn ->
                        let nminus1 = zdAdd `app` zn `app` (ZDV (-1) mempty)
                            ift = zIf   (zLiftFunction $ \x -> ZBool (x <= 0)) -- predicate
                                        (ZDV 0 mempty)                         -- then result
                                        (zdAdd `app` zn `app` (zf `app` nminus1)) -- else result
                        in
                            ift `app` zn

zDownFixed :: ZDExpr (DiffNum Integer -> DiffNum Integer)
zDownFixed = (fix zDownFixable)


instance (T2ZipCombine f1 f2, T2Combine a1 a2) => T2Combine (Cofree f1 a1) (Cofree f2 a2)  where
    type T2Combined (Cofree f1 a1) (Cofree f2 a2) = Cofree (T2ZipCombined f1 f2) (T2Combined a1 a2)
    t2Combine (a0 :< xs0, a1 :< xs1) = (t2Combine (a0, a1) ) :< (t2ZipCombine (xs0,xs1))
    t2Sunder (a :< xs) = let (a0,a1) = t2Sunder a
                             (xs0, xs1) = t2UnzipSunder xs
                         in
                             (a0 :< xs0, a1 :< xs1)

instance (T2ZipCombine f1 f2, T2Combine a1 a2) => T2ZipCombine (CCTC.CofreeF f1 a1) (CCTC.CofreeF f2 a2) where
    type T2ZipCombined (CCTC.CofreeF f1 a1) (CCTC.CofreeF f2 a2) = CCTC.CofreeF (T2ZipCombined f1 f2) (T2Combined a1 a2)
    t2ZipCombine (a0 CCTC.:< xs0, a1 CCTC.:< xs1) = (t2Combine (a0,a1)) CCTC.:< (t2ZipCombine (xs0,xs1))
    t2UnzipSunder (a CCTC.:< xs) = let (a0,a1) = t2Sunder a
                                       (xs0, xs1) = t2UnzipSunder xs
                                   in
                                       (a0 CCTC.:< xs0, a1 CCTC.:< xs1)
-}

-- | 'ZapList' is 'ZipList' with a 'Show1' instance so that 'show' works for @Cofree ZapList a@
newtype ZapList a = ZapList [a]
  deriving (Show, Eq)
  deriving (Hask.Functor, Show1) via []

instance Hask.Foldable ZapList where
  foldMap fm (ZapList as) = Hask.foldMap fm as

instance Hask.Applicative ZapList where
  pure x = ZapList [x]
  liftA2 f (ZapList a) (ZapList b) = ZapList (zipWith f a b)


type ValDeltaCategory = ConstrainedCategory (->) ValDeltaBundle

toValDeltaCategory :: (ValDeltaBundle a, ValDeltaBundle b) => (a -> b) -> ValDeltaCategory a b
toValDeltaCategory = constrained


{-
instance T2ZipCombine ZapList ZapList where
    type T2ZipCombined ZapList ZapList = ZapList
    t2ZipCombine (ZapList as, ZapList bs) = ZapList $ fmap t2Combine $ zip as bs
    t2UnzipSunder (ZapList xs) = let (as,bs) = unzip (fmap t2Sunder xs)
                                 in (ZapList as, ZapList bs)


instance T2Combine Integer Integer where
    type T2Combined Integer Integer = (Integer,Integer)
    t2Combine = id
    t2Sunder  = id
-}
--
-- values for ghci fiddling
--

{-
leaf :: ZapList a
leaf = ZapList []

val :: Cofree ZapList Integer
val = 3 :< ZapList [4 :< leaf, 5 :< leaf]

val2 :: Cofree ZapList Integer
val2 = 10 :< ZapList [5 :< leaf, 2 :< leaf]


listX :: Day (Cofree ZapList) (Cofree ZapList) (Integer,Integer)
listX = Day val val2 (,)
-}


--
-- instances for Day
--

{-testX :: TwoVal (Cofree ZapList) (Cofree ZapList) Integer
testX = TwoVal ChooseOne val val2

distTwoVal :: (Functor f, Distributive w, Distributive v) => f (TwoVal w v a) -> TwoVal w v (f a)
distTwoVal x = TwoVal ChooseOne (distW x) (distV x)
    where
        distW :: (Functor f, Distributive w) => f (TwoVal w v a) -> w (f a)
        distW x = distribute $ fmap (\(TwoVal c wa va) -> wa) x
        distV :: (Functor f, Distributive v) => f (TwoVal w v a) -> v (f a)
        distV x = distribute $ fmap (\(TwoVal c wa va) -> va) x

traverseTwoVal :: (Applicative f, Functor w, Functor v, Distributive f) => TwoVal w v (f a) -> f (TwoVal w v a)
traverseTwoVal (TwoVal c wfa vfa) = let fwa = distribute wfa
                                        fva = distribute vfa
                                    in
                                        liftA2 (TwoVal ChooseOne) fwa fva

addZapList :: (Num a) => ZapList a -> a
addZapList (ZapList zs) = foldl (+) (fromIntegral 0) zs

addCofree :: (Num a) => CCTC.CofreeF ZapList a a -> a
addCofree (a CCTC.:< xs) = a + addZapList xs

addTwofree :: (Num a) => TwoVal (Cofree ZapList) (Cofree ZapList) a -> a
addTwofree x = undefined --_y x

cataAdd :: Cofree ZapList Integer -> Integer
cataAdd = cata addCofree

zipTwo :: TwoVal (Cofree ZapList) (Cofree ZapList) Integer -> (T2Combined (Cofree ZapList Integer) (Cofree ZapList Integer))
zipTwo x = cata vx x

anaZipTwo :: TwoVal (Cofree ZapList) (Cofree ZapList) Integer -> (T2Combined (Cofree ZapList Integer) (Cofree ZapList Integer))
anaZipTwo x = ana avx x

avx :: TwoVal (Cofree ZapList) (Cofree ZapList) Integer -> CCTC.CofreeF ZapList (Integer,Integer) (TwoVal (Cofree ZapList) (Cofree ZapList) Integer)
avx (TwoVal c (a :< ws) (b :< vs)) = (t2Combine (a,b)) CCTC.:< (liftA2 (TwoVal ChooseOne) ws vs)

vx :: TwoValBase (Cofree ZapList) (Cofree ZapList) Integer ((T2Combined (Cofree ZapList Integer) (Cofree ZapList Integer)))
   -> (T2Combined (Cofree ZapList Integer) (Cofree ZapList Integer))
vx (TwoValBase (a CCTC.:< xs)) = (t2Combine a) :< xs

vxx :: CCTC.CofreeF ZapList (Integer,Integer) a -> CCTC.CofreeF ZapList (Integer,Integer) a
vxx (a CCTC.:< xs) = a CCTC.:< xs

instance Num (Integer, Integer) where
    (a0,b0) + (a1,b1) = (a0+a1,b0+b1)
    fromInteger x = (x,x)

foldTwo :: Cofree ZapList (Integer, Integer) -> (Integer, Integer)
foldTwo x = cata addTwoInt x

addTwoInt :: (Num a) => CCTC.CofreeF ZapList a a -> a
addTwoInt (a CCTC.:< xs) = a + (foldl (+) (fromIntegral 0) xs)

fadd :: TwoVal (Cofree ZapList) (Cofree ZapList) Integer -> (Integer, Integer)
fadd x = (cata addTwoInt) . (cata vx) $ x
    where
        fx :: TwoValBase (Cofree ZapList) (Cofree ZapList) Integer (Integer,Integer) -> (Integer, Integer)
        fx = undefined

-- zip up tree and cata it
foldTestX :: TwoVal (Cofree ZapList) (Cofree ZapList) Integer -> (Integer, Integer)
foldTestX = hylo addTwoInt avx


genTree :: Gen a -> Gen (NonEmpty.NonEmpty a)
genTree ga = Gen.nonEmpty (Range.linear 0 10) ga

-}

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
  _name     :: HKD f (ReplaceOnly String)
  } deriving (Generic)

makeLenses ''Thingy

instance (Show (HKD f (ReplaceOnly (Double,Double))),
          Show (HKD f (ReplaceOnly String))
          ) => Show (Thingy f) where
    show (Thingy p n) = "Thingy (" ++ show p ++ ") (" ++ show n ++ ")"

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
-- ValDelta convenience function to treat @ValDelta a@ as @a@ via a lens
-- 
--

valueLens :: (ValDeltaBundle a, Patchable a) => Lens' (ValDelta a) a
valueLens = lens getter setter
  where
    getter = patchVD
    setter dva a' = let (a,_da) = unbundleVD dva
                        da' = changes a a'
                    in bundleVD (a,da')

--
-- Thingy functions
--

thingyToKey :: Thingy 'HKDValDelta -> Int
thingyToKey t = let (ReplaceOnly n) = t ^. name . valueLens
                in hash n

mkThingyVal :: (Double, Double) -> String -> Thingy 'HKDValue
mkThingyVal p n = Thingy (ReplaceOnly p) (ReplaceOnly n)

{-tableOfStuff :: MagicJetTable (Thingy 'HKDValue)
tableOfStuff = fromList thingyToKey $
  fmap (\x -> bundleVD (x,noPatch)) [
  (mkThingyVal (3.0,2.0) "学生"),
  (mkThingyVal (1.0,1.0) "Bob"),
  (mkThingyVal (4.0,5.0) "Blorpshaft")
  ]-}
x = "就这?"

newtype MapX i a = MapX (Map.Map i (ReplaceableValDelta (Maybe a)))

instance Hask.Functor (MapX i) where
  fmap f (MapX m) = MapX $ fmap (fmap (fmap f)) m

mapOfStuff :: Map.Map Integer (ReplaceableValDelta (Maybe (Thingy 'HKDValue)))
mapOfStuff = Map.alter (alterILC (\_->Just $ mkThingyVal (3.0,2.0) "bob")) (3 :: Integer) (Map.fromList [])

alterILC :: (Patchable a, ValDeltaBundle a) => (Maybe a -> Maybe a) -> (Maybe (ReplaceableValDelta (Maybe a))) -> (Maybe (ReplaceableValDelta (Maybe a)))
alterILC f = \x -> case x of
               -- nothing in the map yet
               Nothing -> case (f Nothing) of
                            Nothing -> Nothing
                            Just v' -> Just (ReplaceableValues Nothing (Just v'))
               Just v  -> case v of
                            ReplaceableValDelta vd -> let (a,da) = unbundleVD vd
                                                          fa = f (patch a da)
                                                      in case fa of
                                                        Nothing -> undefined
                                                        a'@(Just _) -> Just (bundleVD (ReplaceableVal a, replaceableChanges a a'))
                            ReplaceableValues a a' -> Just $ ReplaceableValues a (f a')
                            
updateILC :: (Patchable a, ValDeltaBundle a) => (ValDelta a -> ValDelta a) ->  (ReplaceableValDelta (Maybe a) -> ReplaceableValDelta (Maybe a))
updateILC f = \vd -> case vd of
                        ReplaceableValDelta da -> ReplaceableValDelta (fmap f da)
                        ReplaceableValues a a' -> ReplaceableValues a (fmap (autoPatch f) a')

stepPosition :: (Double,Double) -> (Double,Double)
stepPosition (a,b) = (a,b+0.03)

xx :: Maybe (ReplaceableValDelta (Maybe (Thingy 'HKDValue)))
xx = Map.lookup 3 mapOfStuff

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


