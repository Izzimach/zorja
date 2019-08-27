{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Patchable (
    Patchable,
    patch,
    changes, 
    PatchDelta,
    UnPatchDelta,
    ReplaceOnly(..),
    Replacing(..),
    SelfDelta,
    FunctorDelta,
    SelfPatchable(..),
    patchGeneric, 
    changesGeneric
    )
    where

import GHC.Generics

import Data.Kind
import Data.Semigroup
import Data.Group

import Control.Applicative

-- | For a type @a@ there is a delta @PatchDelta a@ that describes how to
--   make changes to @a@ and produce a new value :@patch a (PatchDelta a) = a'@
--
--   We make @PatchDelta@ injective which is a little inconvenient.  It means
--   no two types can have the same type for @PatchDelta@ but it also gives
--   the typechecker more hints to properly digest complex types that use @PatchDelta@.

type family PatchDelta a = da | da -> a
type family UnPatchDelta da = a | a -> da

-- | Certain types have a functor relationship to their delta, so that
-- @PatchDelta a@ can be expressed as @f a@ where @f@ is a functor.

--type family FunctorDelta (f :: Type -> Type) = (a :: Type -> Type) | a -> f
type family FunctorDelta (f :: Type -> Type) = (a :: Type -> Type) | a -> f


-- | unit is it's own delta
type instance (PatchDelta ()) = ()
type instance (UnPatchDelta ()) = ()



-- |
-- | A typeclass for data that can be diff'd and patched.
-- | The associated type @PatchDelta a@ must be a Monoid since it
-- | can be combined with other changes to generate a "combined patch"
-- | and must support an empty patch. Note that this monoid combines small
-- | patches into a single bigger patch, which may be different behavior than
-- | some default Monoid instance for that type. You may have to use a @newtype@
-- | wrapper to distinguish the two.
-- |
-- | @patch x (changes x x') = x'@

class (Monoid (PatchDelta a)) => Patchable a where
  -- | @patch x dx@ applies the changes in @dx@ to @x@
  patch :: a -> PatchDelta a -> a
  -- | @changes x x'@ generates a @dx :: PatchDelta a@ that can convert @x@ into @x'@ using @patch@
  changes ::  a -> a -> PatchDelta a

-- | Some data types are their own delta. We can mark this with a typeclass
-- | See also @SelfPatchable@ which converts any @Group@ into a @SelfDelta@

class (Patchable a) => SelfDelta a where
  valueToDelta :: a -> PatchDelta a
  deltaToValue :: PatchDelta a -> a



-- |
-- | ReplaceOnly is a Patchable type that just replaces the
-- | previous value. Efficient for primitive types, but
-- | larger data structures should use something more clever
-- |

newtype ReplaceOnly a = ReplaceOnly a
    deriving (Eq, Show)

newtype Replacing a = Replacing (Option (Last a))
    deriving (Eq, Show)

type instance PatchDelta (ReplaceOnly a) = Replacing a
type instance FunctorDelta ReplaceOnly = Replacing

instance (Semigroup a) => Semigroup (ReplaceOnly a) where
    (ReplaceOnly a) <> (ReplaceOnly b) = ReplaceOnly (a <> b)

instance (Monoid a) => Monoid (ReplaceOnly a) where
    mempty = ReplaceOnly mempty

instance (Eq a) => Patchable (ReplaceOnly a) where
  patch a (Replacing da) =
      case getOption da of
          Nothing -> a
          Just (Last a') -> ReplaceOnly a'
  changes (ReplaceOnly a) (ReplaceOnly b) =
      if (a == b)
      then Replacing $ Option Nothing
      else Replacing $ Option $ Just $ Last b

instance Functor ReplaceOnly where
    fmap f (ReplaceOnly x) = ReplaceOnly (f x)

instance Applicative ReplaceOnly where
    pure x = ReplaceOnly x
    (ReplaceOnly a) <*> (ReplaceOnly b) = ReplaceOnly (a b)

instance (Num a) => Num (ReplaceOnly a) where
    a + b = liftA2 (+) a b
    a * b = liftA2 (*) a b
    abs a = fmap abs a
    signum a = fmap signum a
    negate a = fmap negate a
    fromInteger n = ReplaceOnly (fromInteger n)

instance (Ord a) => Ord (ReplaceOnly a) where
    (ReplaceOnly a) <= (ReplaceOnly b) = a <= b


instance Functor Replacing where
    fmap f (Replacing a) = Replacing $ fmap (fmap f) a

instance Applicative Replacing where
    pure x = Replacing $ pure $ pure x
    (Replacing fab) <*> (Replacing a) = Replacing (liftA2 (<*>) fab a)

instance Semigroup (Replacing a) where
    (Replacing a) <> (Replacing b) = Replacing (a <> b)

instance Monoid (Replacing a) where
    mempty = Replacing mempty
    
    
--
-- | Patchable instance for functions
--

type instance PatchDelta (a -> b) = a -> PatchDelta a -> PatchDelta b

instance (Patchable a, Patchable b) => Patchable (a -> b) where
    patch f ev = \a -> patch (f a) (ev a mempty)
    changes f1 f2 = \a -> \da ->
        --
        -- Incorporate both f' and delta-f:
        --
        -- f' uses the change da:
        --   b1' = (f1 a) + (f1' a da)
        --
        -- delta-f doesn't handle the change da. Instead it is the change between f1
        -- and f2 when they are given the same argument value:
        --   "delta-f at a" = changes (f1 a) (f2 a)
        --   "delta-f at a'" = changes (f1 a') (f2 a')
        -- Note that delta-f may be different at different values of a
        -- 
        -- 
        let b1  = f1 a
            a' = patch a da
            --b1' = f1 a'           -- this represents (f1 a) + (f1' a da)
            b2' = f2 a'             -- delta-f from f1 to f2 at a':
                                    -- changes (f1 a) (f2 a) is delta-f at a
                                    -- changes (f1 a') (f2 a') is delta-f at a'
        in
            -- (changes b2' b1') <> (changes b1' b1) = changes b2' b1
            changes b2' b1

{- type inst  ance PatchDelta ((->) a b) = (a -> b) -> (a -> b)


instance (Monoid b, Patchable b) => Patchable ((->) a b) where
    patch f df = df f
    changes f f' = \xf -> 
                        -- we don't know what's in xf, so instead of patching
                        -- xf directly we patch the return value of xf
                        \a -> let x = xf a
                                  b = f a
                                  b' = f' a
                              in patch x ((changes x b) <> (changes b b'))
-}

--
-- | Patchable tuples. In this case we just patch
--   each component independently, which may not be what
--   you want.
--

type instance PatchDelta (a,b) = (PatchDelta a, PatchDelta b)

instance (Patchable a, Patchable b) => Patchable (a,b) where
    patch (a,b) (da,db) = (patch a da, patch b db)
    changes (a0,b0) (a1,b1) = (changes a0 a1, changes b0 b1)
  

--
-- | If a is a group, we can generate a Patchable type where the 
--   delta is the same type as the actual value.
--   Patches are performed using semigroup (<>).
--   Works for some numbers (Integer) but for others you
--   have the problem that some values are unrepresentable.  For instance,
--   (changes a a') on float may produce a delta that is too small to
--   represent as a float.
--
--   We need @a@ to be a group since computing @changes@ requires the inverse of @a@
--

data SelfPatchable a = SelfPatchable a deriving (Eq, Show)


type instance PatchDelta (SelfPatchable a) = SelfPatchable a

instance (Group a) => SelfDelta (SelfPatchable a) where
    valueToDelta a = a
    deltaToValue da = da
    
instance Functor SelfPatchable where
    fmap f (SelfPatchable x) = SelfPatchable (f x)

instance Applicative (SelfPatchable) where
    pure x = SelfPatchable x
    (SelfPatchable a) <*> (SelfPatchable b) = SelfPatchable (a b)

instance (Semigroup a) => Semigroup (SelfPatchable a) where
    (SelfPatchable a) <> (SelfPatchable b) = SelfPatchable (a <> b)

instance (Monoid a) => Monoid (SelfPatchable a) where
    mempty = SelfPatchable mempty

instance (Num a) => Num (SelfPatchable a) where
    a + b = liftA2 (+) a b
    a * b = liftA2 (*) a b
    abs a = fmap abs a
    signum a = fmap signum a
    negate a = fmap negate a
    fromInteger n = SelfPatchable (fromInteger n)

instance (Group a) => Patchable (SelfPatchable a) where
    patch (SelfPatchable a) (SelfPatchable da) = SelfPatchable (a <> da)
    changes (SelfPatchable a) (SelfPatchable b) = SelfPatchable ((invert a) <> b)

instance (Ord a) => Ord (SelfPatchable a) where
    (SelfPatchable a) <= (SelfPatchable b) = a <= b


--
-- patchable lists
--

data ListDelta a = PatchNode (PatchDelta a) (ListDelta a)
                 | KeepList

type instance (PatchDelta [a]) = ListDelta a

instance (Patchable a) => Semigroup (ListDelta a) where
    a <> KeepList = a
    KeepList <> a = a
    (PatchNode a as) <> (PatchNode a' as') = PatchNode (a <> a') (as <> as')

instance (Patchable a) => Monoid (ListDelta a) where
    mempty = KeepList

instance (Patchable a) => Patchable [a] where
    patch x KeepList = x
    patch (x:xs) (PatchNode a as) = (patch x a) : patch xs as
    patch [] _x = undefined   -- can't patch empty node!
    changes _x _x' = undefined

--
-- Patchable generics, useful for records or extended sum types
--



class PatchG i o where
  patchG :: i p -> o p -> i p
  changesG :: i p -> i p -> o p

instance (Patchable x, dx ~ PatchDelta x) => PatchG (K1 a x) (K1 a dx) where
  patchG :: K1 a x p -> K1 a (PatchDelta x) p -> K1 a x p
  patchG (K1 x) (K1 dx) = K1 $ patch x dx
  changesG :: K1 a x p -> K1 a x p -> K1 a (PatchDelta x) p
  changesG (K1 x0) (K1 x1) = K1 $ changes x0 x1
  

instance (PatchG i o, PatchG i' o') => PatchG (i :*: i') (o :*: o') where
  patchG (l0 :*: r0) (l1 :*: r1) = (patchG l0 l1) :*: (patchG r0 r1)
  changesG (l0 :*: r0) (l1 :*: r1) = (changesG l0 l1) :*: (changesG r0 r1)

--
-- patch for a sum type allow patching a current value (left choices),
-- or switching to a separate value (right choices)
--
-- this means the change type for (A | B) would be:
--   (A :+: B :+: (PatchDelta (A | B)))
--

instance (PatchG i o, PatchG i' o')
    => PatchG (i :+: i') (i :+: i' :+: o :+: o') where
  patchG (L1 a) (R1 (R1 (L1 da))) = L1 $ patchG a da
  patchG _ (R1 (L1 b))  = R1 $ b
  patchG (R1 b) (R1 (R1 (R1 db))) = R1 $ patchG b db
  patchG _ (L1 a)  = L1 $ a
  -- these should not occur, sigh
  patchG (L1 _) (R1 (R1 (R1 _))) = undefined
  patchG (R1 _) (R1 (R1 (L1 _))) = undefined

  
  changesG (L1 a) (L1 a') = R1 . R1 . L1 $ changesG a a'
  changesG (L1 _) (R1 b)  = R1 . L1 $ b
  changesG (R1 _) (L1 a)  = L1 $ a
  changesG (R1 b) (R1 b') = R1 . R1 . R1  $ changesG b b'

instance (PatchG i o) => PatchG (M1 _a _b i) (M1 _a' _b' o) where
  patchG   (M1 x) (M1 dx) = M1 $ patchG x dx
  changesG (M1 x) (M1 y)  = M1 $ changesG x y


instance PatchG V1 V1 where
  patchG   = undefined
  changesG = undefined

instance PatchG U1 U1 where
  patchG U1 U1   = U1
  changesG U1 U1 = U1

--
-- PatchDelta for generics
--



patchGeneric ::
  (Generic f,
   Generic (PatchDelta f),
--    Monoid (PatchDelta f),
   PatchG (Rep f) (Rep (PatchDelta f)))
  => f -> (PatchDelta f) -> f
patchGeneric a da = to $ patchG (from a) (from da)

changesGeneric ::
  (Generic f,
   Generic (PatchDelta f),
   PatchG (Rep f) (Rep (PatchDelta f)))
  => f -> f -> (PatchDelta f)
changesGeneric a b = to $ changesG (from a) (from b)  
  
--  patch a da = to $ patchG (from a) (from da)
--  changes a a' = to $ changesG (from a) (from a')


--
-- The patchable for a sum type @a@ has two constructors:
--  - NewSum @a@ replaces the current val with the new value @a@. For
--        a sum type this is how you switch to a different constructor
--  - PatchSum @da@ applies the patch @da@ to the current value. The type
--        of @da@ is the Patchable of the constructor of the current value.
--

