{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Zorja.ZCCC where

import Zorja.Patchable

import Data.Kind (Constraint)

--
-- Class and datatypes to build functions as elements of a
-- Cartesian Closed Category (CCC) which can be composed with
-- other functions. See Conal Elliot's "Compiling to Categories"
--

-- Generally you will build your low-level functions by embedding them into
-- the @ZD@ datatype which represents a function (a -> b) and its
-- change (a -> PatchDelta a -> PatchDelta b). Then you can take @ZD@
-- types and compose them using `zdot` which is equivalent to (.)


--
-- Definition of Category including constraints
--

class ZCategory k where
  type Ok k a :: Constraint
  type Ok k a = Patchable a
  id :: Ok k a => a `k` a
  zdot :: (Ok3 k a b c) => (b `k` c) -> (a `k` b) -> (a `k` c)

type Ok2 k a b = (Ok k a, Ok k b)
type Ok3 k a b c = (Ok k a, Ok k b, Ok k c)

--
-- For a given pair of types a and b, we need two functions:
--  a -> b
--  PatchDelta a -> PatchDelta b
--
-- The first one is just the (->) constructor. We use
-- JetD to represent the second function.
--
-- So for a `k` b:
--    k = (->) gives a normal function (a -> b)
--    k = JetD gives a delta function (PatchDelta a -> PatchDelta b)
--

newtype JetD a b = JetD { unJetD :: PatchDelta a -> PatchDelta b }

instance ZCategory (JetD) where
  type Ok JetD a = Patchable a
  id                         = JetD (\x -> x)
  zdot (JetD zbc) (JetD zab) = JetD (zbc . zab)


--
-- ZD represents the compacted form of incremental functions described in
-- compiling to categories: @a -> (b, PatchDelta a -> PatchDelta b)@
--
-- Here @PatchDelta a -> PatchDelta b@ is @a `k` b@ where @k@ is @JetD@
--

newtype ZD k a b = ZD { unZD :: a -> (b, a `k` b) }

instance ZCategory k => ZCategory (ZD k) where
  type Ok (ZD k) a = Ok k a
  id           = ZD $ \a -> (a,Zorja.ZCCC.id)
  zdot zbc zab = ZD $ \a -> let (b, db) = (unZD zab) a
                                (c, dc) = (unZD zbc) b
                            in (c, dc `zdot` db)
                       

--
-- Lift a generic haskell function into ZCategory space. This
-- lets us compose functions with derivatives.
--

liftZDJet :: (Ok2 JetD a b, Patchable a, Patchable b) => (a -> b) -> ZD JetD a b
liftZDJet f = ZD $ \a -> let b = f a
                         in (b,
                             JetD $ \da -> let b' = f $ patch a da
                                           in (changes b b'))

