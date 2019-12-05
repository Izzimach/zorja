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

import Data.Monoid (Sum(..))
import Data.Functor.Foldable


import Control.Monad.State

import Zorja.Patchable
import Zorja.Primitives

--import Zorja.Collections.FAlgebra

import Fcf

import Zorja.ZHOAS
import Zorja.FunctorDExpr
import Zorja.Collections.ListX

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


testList :: RFType (ListXK ReplaceOnlyK) Int
testList = RFT $ ListX $ [
               ReplaceOnly 3,
               ReplaceOnly 5
            ]

testListD :: RFTypeD (ListXK ReplaceOnlyK) Int
testListD = RFTD $ ListXD $ [
                Replacing Nothing,
                Replacing (Just 6)
            ]

testListFDE :: ZFExpr (ListXK ReplaceOnlyK) Int
testListFDE = ZFE testList testListD


-- | try a catamorphism...
-- - starting with a @ZFExpr (ListXK ReplaceOnlyK) Int@
-- - unfold into a ListX with coalListXFDE
-- - then fold up with mergeListXFDE
testListCata :: ZFExpr ReplaceOnly Int
testListCata = undefined --cata _f testListFDE


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
