{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

--
-- | A "Scratch Buffer" used for experimental code.
--

module Blackboard where

--import Data.Monoid (Sum(..))
import Data.Functor.Foldable
import Data.Distributive
import Data.Functor.Rep


import Control.Monad.State

import Control.Comonad
import Control.Applicative
import Control.Comonad.Env
--import Control.Comonad.Cofree
import Control.Comonad.Trans.Cofree
import Control.Comonad.Store

--import Zorja.Patchable
import Zorja.Primitives


import Zorja.ZHOAS
import Zorja.FunctorDExpr

--import Zorja.Collections.ZJIntMap
--import Zorja.Collections.Cofree

--
-- recursive deltas
--

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

--
-- experiments with F-Algebra
--


testList :: ZList ZIdentity 'HKTValue Int
testList = ZList $ [
               ZIdentity 3,
               ZIdentity 5
            ]

testListD :: ZList ZIdentity 'HKTDelta Int
testListD = ZList $ [
                ZDIdentity 3,
                ZDIdentity 6
            ]

leaf :: [a]
leaf = []

val :: Cofree [] Integer
val = cofree $ 3 :< [cofree $ 4 :< leaf, cofree $ 5 :< leaf]

val2 :: Cofree [] Integer
val2 = cofree $ 10 :< leaf

data WhichTree = TreeOne | TreeTwo

data TwoTree w v a = TwoTree WhichTree (w a) (v a)

class TwoTreeZip f where
    twoTreeZip :: WhichTree -> f (w a) -> f (v a) -> f (TwoTree w v a)

instance TwoTreeZip [] where
    twoTreeZip b xs ys = zipWith (\x y -> TwoTree b x y) xs ys

twoWrap :: a -> a -> (WhichTree -> a)
twoWrap a1 a2 = branchA
    where
        branchA TreeOne = a1
        branchA TreeTwo = a2

twoWrapCofree :: Applicative f => WhichTree -> Cofree f a -> Cofree f a -> Cofree f (TwoTree (Cofree f) (Cofree f) a)
twoWrapCofree b t1 t2 = let x1 = unwrap t1
                            x2 = unwrap t2
                        in
                            cofree $ TwoTree b t1 t2 :< (liftA2 (twoWrapCofree b) x1 x2)

instance (Functor w, Functor v) => Functor (TwoTree w v) where
    fmap f (TwoTree b t1 t2) = TwoTree b (fmap f t1) (fmap f t2)

instance (Comonad w, Comonad v) => Comonad (TwoTree w v) where
    extract (TwoTree TreeOne wa _va) = extract wa
    extract (TwoTree TreeTwo _wa va) = extract va
    duplicate (TwoTree b wa va) = TwoTree b (twoW wa va) (twoV wa va)
        where
            twoW :: w a -> v a -> w (TwoTree w v a)
            twoW wa va = extend (\w -> TwoTree TreeOne w va) wa
            twoV :: w a -> v a -> v (TwoTree w v a)
            twoV wa va = extend (\v -> TwoTree TreeTwo wa v) va

instance (Functor f, TwoTreeZip f, ComonadCofree f w, ComonadCofree f v) => ComonadCofree f (TwoTree w v) where
    unwrap (TwoTree b wa va) = twoTreeZip b (unwrap wa) (unwrap va)

data Blargh a = Blargh Bool a

thing :: CofreeT [] Blargh Integer
thing = CofreeT (Blargh True (3 :< []))

{-instance (Applicative f, Applicative g) => Comonad (TwoTree (Cofree f) (Cofree g)) where
    extract (TwoTree TreeOne t1 _) = extract t1
    extract (TwoTree TreeTwo _ t2) = extract t2
    duplicate (TwoTree b t1 t2) = TwoTree b (twoWrapCofree TreeOne t1 t2) (twoWrapCofree TreeTwo t1 t2)

instance (Comonad (TwoTree w v), Comonad w, Comonad v) => ComonadStore WhichTree (TwoTree w v) where
    pos (TwoTree b _ _) = b
    peek TreeOne (TwoTree _ t1 _) = extract t1
    peek TreeTwo (TwoTree _ _ t2) = extract t2
    seek b (TwoTree _ t1 t2) = TwoTree b t1 t2


twoExtract :: ComonadStore WhichTree w => w a -> (a,a)
twoExtract tt = let v1 = extract (seek TreeOne tt)
                    v2 = extract (seek TreeTwo tt)
                in (v1,v2)
-}

newtype DoubleCofree f a = DCF (StoreT WhichTree (Cofree f) a)

doubleWCofree :: Applicative f => Cofree f a -> Cofree f a -> Cofree f (WhichTree -> a)
doubleWCofree (a1 :< x1) (a2 :< x2) = branchA a1 a2 :< (liftA2 doubleWCofree x1 x2)
    where
        branchA a _ TreeOne = a
        branchA _ b TreeTwo = b

doubleCofree :: (Applicative f) => Cofree f a -> Cofree f a -> WhichTree -> DoubleCofree f a
doubleCofree cf1 cf2 b = DCF $ StoreT (doubleWCofree cf1 cf2) b

data TwoThing a = TTH a a

data TwoThingIndex = FirstThing | SecondThing

getThing :: TwoThing a -> TwoThingIndex -> a
getThing (TTH a _) FirstThing = a
getThing (TTH _ b) SecondThing = b

instance Functor TwoThing where
    fmap f (TTH a b) = TTH (f a) (f b)

instance Distributive TwoThing where
    distribute fa = TTH (fmap ttfst fa) (fmap ttsnd fa)
        where
            ttfst = flip getThing FirstThing
            ttsnd = flip getThing SecondThing

instance Representable TwoThing where
    type Rep (TwoThing) = TwoThingIndex
    tabulate f = TTH (f FirstThing) (f SecondThing)
    index = getThing

{-testTreez :: CofD (ZJItemMap FNotWrapped) ReplaceOnly (Sum Int)
testTreez = (ReplaceOnly 3)
                :<<
                zjItemMapFromList [
                    FNotWrapped $ (ReplaceOnly (Sum 4)) :<< zjItemMapFromList [], 
                    FNotWrapped $ (ReplaceOnly (Sum 5)) :<< zjItemMapFromList []
                ]

testTreezD :: CofDD (ZJItemMap FNotWrapped) ReplaceOnly (Sum Int)
testTreezD = (Replacing Nothing)
                 :<#
                 zjItemMapDFromList [] []

testTreeFDE :: FunctorDExpr (CofD (ZJItemMap FNotWrapped) ReplaceOnly) (Sum Int)
testTreeFDE = FDE testTreez testTreezD


-}
main :: IO ()
main = return ()
