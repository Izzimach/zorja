{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Zorja.Jet where

--
-- access Generic from and to as G.from and G. to
--
import GHC.Generics hiding (from, to)
import qualified GHC.Generics as G

import Zorja.Patchable

import Control.Lens


--
-- @Jet@ bundles a value and its delta into a single record.
--

data Jet a = Jet
  {
    position :: a, 
    velocity :: PatchDelta a
  }

toJet :: (Patchable a) => a -> Jet a
toJet x = Jet { position = x, velocity = mempty }


deriving instance (Eq a, Eq (PatchDelta a), Patchable a) => Eq (Jet a)
deriving instance (Show a, Show (PatchDelta a), Patchable a) => Show (Jet a)



-- A PatchedJet contains patch data and the value AFTER the
-- patch has been applied. This is useful when composing functions
-- that produce and accumulate patch data. Otherwise when composing
-- we have to always apply 'patch a da' to get the most up-to-date
-- changed value.

data PatchedJet a = PatchedJet
  {
    patchedval :: a, 
    history :: PatchDelta a 
  }
  deriving (Generic)

deriving instance (Eq a, Eq (PatchDelta a), Patchable a) => Eq (PatchedJet a)
deriving instance (Show a, Show (PatchDelta a), Patchable a) => Show (PatchedJet a)

toPatchedJet :: (Patchable a) => a -> PatchedJet a
toPatchedJet a = PatchedJet a mempty

fromPatchedJet :: PatchedJet a -> a
fromPatchedJet = patchedval



--
-- PatchedJet lenses for 2-tuples
--

instance 
  Field1 (PatchedJet (a,b)) (PatchedJet (a,b)) (PatchedJet a) (PatchedJet a)
    where
  _1 k (PatchedJet (a,b) (da,db)) = 
    let x' = k (PatchedJet a da)
        lxify = \(PatchedJet a' da') -> PatchedJet (a',b) (da', db)
    in fmap lxify x'
  

instance 
  Field2 (PatchedJet (a,b)) (PatchedJet (a,b)) (PatchedJet b) (PatchedJet b)
    where
  _2 k (PatchedJet (a,b) (da,db)) = 
    let x' = k (PatchedJet b db)
        lxify = \(PatchedJet b' db') -> PatchedJet (a,b') (da, db')
    in fmap lxify x'

--
-- lenses for HKD records via generics
-- from Sandy Maguire's "Thinking With Types"
--

data LensFor s a = LensFor
  { getLensFor :: Lens' s a }

class HKDLenses z i o where
  -- the input (i p) is a lens from the HKD record to
  -- the Generic rep, built by 'iso from to' in getHKDLenses
  -- and the return value (o p) is the Generic rep with the
  -- Lenses 'inside' so basically the Generic instances
  -- either build the Lens (for K1) or wrap the Generic
  -- constructors around whatever lens is there.
  gHKDlenses :: Lens' (z Identity) (i p) -> o p

instance HKDLenses z (K1 _x a)
                     (K1 _x (LensFor (z Identity) a)) where
  gHKDlenses l = K1
                 $ LensFor
                 $ \f -> l $ fmap K1 . f . unK1
  {-# INLINE gHKDlenses #-}

instance (HKDLenses z i o) => HKDLenses z (M1 _a _b i) (M1 _a _b o) where
  gHKDlenses l = M1 $ gHKDlenses $ \f -> l $ fmap M1 . f . unM1
  {-# INLINE gHKDlenses #-}

instance (HKDLenses z i o, HKDLenses z i' o') => HKDLenses z (i :*: i') (o :*: o') where
  gHKDlenses l = gHKDlenses (\f -> l (\(a :*: b) -> fmap (:*: b) $ f a))
             :*: gHKDlenses (\f -> l (\(a :*: b) -> fmap (a :*:) $ f b))
  {-# INLINE gHKDlenses #-}

instance HKDLenses z V1 V1 where
  gHKDlenses _ = undefined

instance HKDLenses z U1 U1 where
  gHKDlenses _ = U1

getHKDLenses :: forall z.
  ( Generic (z Identity),
    Generic (z (LensFor (z Identity))),
    HKDLenses z (Rep (z Identity)) (Rep (z (LensFor (z Identity)))) )
          => z (LensFor (z Identity))
getHKDLenses = G.to $ gHKDlenses @z $ iso G.from G.to


--
-- lens for PatchDelta records
--

data PData a

data LensForDelta s a = LensForDelta
  { getLensForDelta :: Lens' s a }


class HKDDeltaLenses z i o where
  -- the input (i p) is a lens from the HKD record to
  -- the Generic rep, built by 'iso from to' in getHKDLenses
  -- and the return value (o p) is the Generic rep with the
  -- Lenses 'inside' so basically the Generic instances
  -- either build the Lens (for K1) or wrap the Generic
  -- constructors around whatever lens is there.
  gHKDDeltaLenses :: Lens' (z PData) (i p) -> o p

instance HKDDeltaLenses z (K1 _x a)
                      (K1 _x (LensForDelta (z PData) a)) where
  gHKDDeltaLenses l = K1
                      $ LensForDelta
                      $ \f -> l $ fmap K1 . f . unK1
  {-# INLINE gHKDDeltaLenses #-}

instance (HKDDeltaLenses z i o) => HKDDeltaLenses z (M1 _a _b i) (M1 _a _b o) where
  gHKDDeltaLenses l = M1 $ gHKDDeltaLenses $ \f -> l $ fmap M1 . f . unM1
  {-# INLINE gHKDDeltaLenses #-}

instance (HKDDeltaLenses z i o, HKDDeltaLenses z i' o') => HKDDeltaLenses z (i :*: i') (o :*: o') where
  gHKDDeltaLenses l = gHKDDeltaLenses (\f -> l (\(a :*: b) -> fmap (:*: b) $ f a))
                  :*: gHKDDeltaLenses (\f -> l (\(a :*: b) -> fmap (a :*:) $ f b))
  {-# INLINE gHKDDeltaLenses #-}

instance HKDDeltaLenses z V1 V1 where
  gHKDDeltaLenses _ = undefined

instance HKDDeltaLenses z U1 U1 where
  gHKDDeltaLenses _ = U1
  

getHKDDeltaLenses :: forall z.
  (  Generic ((z PData)),
     Generic (z (LensForDelta ( (z PData)))),
     HKDDeltaLenses z (Rep ((z PData))) (Rep (z (LensForDelta ((z PData))))))
          => z (LensForDelta ((z PData)))
getHKDDeltaLenses = G.to $ gHKDDeltaLenses @z $ iso G.from G.to


--
-- HKD for patchedjet lenses.
--

data PJLensFor s a = PJLensFor
  { getPJLensFor :: Lens' (PatchedJet s) (PatchedJet a) }

class PJHKDLenses z i o where
  -- the input (i p) is a lens from the HKD record to
  -- the Generic rep, built by 'iso from to' in getPJHKDLenses
  -- and the return value (o p) is the Generic rep with the
  -- Lenses 'inside' so basically the Generic instances
  -- either build the Lens (for K1) or wrap the Generic
  -- constructors around whatever lens is there.
  gPJHKDLenses :: Lens' (PatchedJet (z Identity)) (i p) -> o p

instance {-(Patchable (z Identity)) => -} PJHKDLenses z (K1 _x (PatchedJet a))
                   (K1 _x (PJLensFor (z Identity) a)) where
  gPJHKDLenses l = K1
                    $ PJLensFor
                    $ \f -> (l $ fmap K1 . f . unK1)
  {-# INLINE gPJHKDLenses #-}

instance {-# OVERLAPPING #-} 
    PJHKDLenses z (M1 D ('MetaData "PatchedJet" _1 _2 _3) i)
                  (M1 D _x  o) where
  gPJHKDLenses _l = M1 $ undefined
      
instance {-# OVERLAPPING #-} (PJHKDLenses z i o) => PJHKDLenses z (M1 _a _b i) (M1 _a _b o) where
  gPJHKDLenses l = M1 $ gPJHKDLenses $ \f -> l $ fmap M1 . f . unM1
  {-# INLINE gPJHKDLenses #-}

instance (PJHKDLenses z i o, PJHKDLenses z i' o') => PJHKDLenses z (i :*: i') (o :*: o') where
  gPJHKDLenses l = gPJHKDLenses (\f -> l (\(a :*: b) -> fmap (:*: b) $ f a))
               :*: gPJHKDLenses (\f -> l (\(a :*: b) -> fmap (a :*:) $ f b))
  {-# INLINE gPJHKDLenses #-}

instance PJHKDLenses z V1 V1 where
  gPJHKDLenses _ = undefined

instance PJHKDLenses z U1 U1 where
  gPJHKDLenses _ = U1


getPJHKDLenses :: forall z.
  ( Generic (PatchedJet (z Identity)),
    Generic (z (PJLensFor (z Identity))),
    PJHKDLenses z (Rep (PatchedJet (z (Identity))))
                  (Rep (z (PJLensFor (z Identity)))) )
          => z (PJLensFor (z Identity))
getPJHKDLenses = G.to $ gPJHKDLenses @z $ iso G.from G.to




--
-- other stuff
--

class GVal i o where
  gval :: i p -> o p

instance GVal (K1 x a) (K1 y a) where
  gval a = K1 $ unK1 a

instance {-# OVERLAPPING #-} (GVal i o) =>
      GVal (M1 D ('MetaData "PatchedJet" b c d) i) 
           (M1 D ('MetaData "PatchedJet" b c d) o) where
  gval x = M1 $ gval (unM1 x)

instance (GVal i o) => GVal (M1 a b i) (M1 a b o) where
  gval x = M1 $ gval (unM1 x)

instance GVal U1 U1 where
  gval U1 = U1
      
instance (GVal a a', GVal b b') => GVal (a :+: b) (a' :+: b') where
  gval (L1 a) = L1 $ gval a
  gval (R1 b) = R1 $ gval b

instance (GVal a a', GVal b b') => GVal (a :*: b) (a' :*: b') where
  gval (a :*: b) = (gval a) :*: (gval b)



instance (Patchable a) => Wrapped (PatchedJet a) where
  type Unwrapped (PatchedJet a) = a
  _Wrapped' = iso patchedval toPatchedJet
