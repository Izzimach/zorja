{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.Patchable (
    Patchable,
    patch,
    changes,
    diffBundle,
    PatchInstance,
    mergePatches,
    (<^<),
    ILCDelta,
    ValDelta,
    ValDeltaBundle,
    ValDeltaMap,
    mapVD,
    bundleVD,
    unbundleVD,
    valueBundle,
    valueUnbundle,
    deltaUnbundle,
    liftVD,
    lowerVD,
    valueLens,
    SeparableFunction(..),
    unSeparated,
    Jet(..),
    SelfPatchable(..),
    patchGeneric,
    changesGeneric,
    combineGeneric,
    bundleVDGeneric,
    unbundleVDGeneric,
    BoolVD(..)
    )
    where

import GHC.Generics

import Data.Group

import Control.Applicative
import qualified Control.Category as C

-- | For a type @a@ there is a delta @ILCDelta a@ that describes how to
--  make changes to @a@ and produce a new value: @patch a (ILCDelta a) = a'@
--  ILC in this case is "Incremental Lambda Calculus"
type family ILCDelta a = da | da -> a


-- | Class for combining 'ILCDelta' values.
-- Two patches can be combined. If we have two patches @da@ and @da'@ then
-- they can be combined into one patch @da <^< da'@, such that:
-- @patch a (da <^< da') = patch (patch a da) da'@.
-- This is distinct from 'Monoid' since merging patches might be different
-- than 'mappend'
--
class PatchInstance a where
    (<^<) :: a -> a -> a

    default (<^<) :: (Generic a, PatchInstanceG (Rep a)) => a -> a -> a
    (<^<) = combineGeneric

-- | 'mergePatches' is a synonym for '(<^<)'
mergePatches :: (PatchInstance a) => a -> a -> a
mergePatches = (<^<)


-- | A @ValDelta@ is a value and it's delta bound together. Often this is
--   just a tuple '(a, ILCDelta a)' or the equivalent 'Jet1 a' but in some cases this may be some
--   other type for complicated or container types.
--   For example 'ValDelta [a]' might be '[(a, ILCDelta a)]' instead of '([a],[ILCDelta a])'
--
type family ValDelta a = ja | ja -> a

class ValDeltaBundle a where
    bundleVD :: (a, ILCDelta a) -> ValDelta a

    default bundleVD ::
      (Generic a, 
      Generic (ILCDelta a), 
      Generic (ValDelta a),
      ValDeltaBundleG (Rep a) (Rep (ILCDelta a)) (Rep (ValDelta a)))
      => (a, ILCDelta a) -> ValDelta a
    bundleVD = bundleVDGeneric

    unbundleVD :: ValDelta a -> (a, ILCDelta a)

    default unbundleVD ::
      (Generic a,
      Generic (ILCDelta a),
      Generic (ValDelta a),
      ValDeltaBundleG (Rep a) (Rep (ILCDelta a)) (Rep (ValDelta a)))
      => ValDelta a -> (a, ILCDelta a)
    unbundleVD = unbundleVDGeneric

    -- | Given a value @a@ generates a @ValDelta a@ with a value of @a@
    --   and a no-op patch value. @patch (valueBundle x) = x@
    valueBundle :: a -> ValDelta a

valueUnbundle :: (ValDeltaBundle a) => ValDelta a -> a
valueUnbundle = fst . unbundleVD

deltaUnbundle :: (ValDeltaBundle a) => ValDelta a -> ILCDelta a
deltaUnbundle = snd . unbundleVD

-- |'Patchable' is a typeclass for data that can be diff'd and patched.
--  The associated type @ILCDelta a@ must be a 'PatchInstance' since it
--  can be combined with other changes to generate a "combined patch"
--  and must support an empty patch. Note that even though 'PatchInstance'
--  is a 'Monoid' that combines small
--  patches into a single bigger patch, it may have different behavior than
--  some default 'Monoid' instance for that type. You may have to use a newtype
--  wrapper to distinguish the two.
-- 
--  @patch x (changes x x') = x'@
class (ValDeltaBundle a, PatchInstance (ILCDelta a)) => Patchable a where
  -- | @patch (bundleVD x dx)@ applies the changes in @dx@ to @x@ producing @x'@
  patch :: ValDelta a -> a
  --default patch :: (Generic a, Generic (ILCDelta a), PatchableG (Rep a) (Rep (ILCDelta a))) => ValDelta a -> a
  --patch = patchGeneric

  -- | @changes x x'@ generates a @dx :: ILCDelta a@ that can convert @x@ into @x'@ using @patch@
  changes ::  a -> a -> ILCDelta a
  changes a a' = snd $ unbundleVD $ diffBundle a a'

  --default changes :: (Generic a, Generic (ILCDelta a), PatchableG (Rep a) (Rep (ILCDelta a))) => a -> a -> ILCDelta a
  --changes = changesGeneric

  -- | Runs changes and bundles up the delta with the original value.
  --   Given two values @a@ and @a'@ then @aa = bundleChanges a a'@ means that
  --   @unbundle aa = (a, changes a a')@ and @patch aa = a'@
  diffBundle :: a -> a -> ValDelta a
  diffBundle a a' = let da = changes a a'
                    in bundleVD (a,da)


-- | For some data types the delta values do not depend or derive from their
--   associated values. In this case we can map between two deltas without
--   computing or accessing the values.
data SeparableFunction a b =
    Separable {
        valueFunction :: a -> b,
        deltaFunction :: ILCDelta a -> ILCDelta b
    }

instance C.Category SeparableFunction  where
    (Separable f df) . (Separable g dg) = Separable (f . g) (df . dg)
    id = Separable id id

unSeparated :: (ValDeltaBundle a, ValDeltaBundle b) => SeparableFunction a b -> (ValDelta a -> ValDelta b)
unSeparated (Separable f df) =
    \va ->  let (a,da) = unbundleVD va
                b = f a
                db = df da
            in
                bundleVD (b,db)

                        
class ValDeltaMap f where
    mapVD :: (Patchable a, Patchable b) => (ValDelta a -> ValDelta b) -> f a -> f b


-- | Given a function from 'a -> b' this will generate a function 'ValDelta a -> ValDelta b'
--   that applies the function to BOTH the original and patched value.
--   It won't be efficient but hopefully it will be correct.
--   If you want to modify the patched value while leaving the original intact, you can
--   use 'valueLens'
liftVD :: (Patchable a, Patchable b)
    => (a -> b) -> (ValDelta a) -> (ValDelta b)
liftVD f = \vda ->  let (a,_da) = unbundleVD vda
                        b = f a
                        b' = f (patch vda)
                    in diffBundle b b'


-- | Given a function from 'ValDelta a -> ValDelta b' this converts it to 'a -> b'
lowerVD :: (Patchable a, Patchable b) => (ValDelta a -> ValDelta b) -> (a -> b)
lowerVD df = \a -> patch $ df $ valueBundle a


--
-- | A lens to modify the patched value in a 'ValDelta', updating the delta value but
--   preserving the original value. Use as a lens, for example @v ^. valueLens@ gets
--   the patched value of @v@
valueLens :: forall f a. (Functor f, Patchable a) => (a -> f a) -> ValDelta a -> f (ValDelta a)
valueLens f vd = let (a,_da) = unbundleVD vd
                     a' = f (patch vd)
                     bundleUp = \x -> diffBundle a x
                 in
                     fmap bundleUp a'

--
-- | Patching for ()
--
type instance (ILCDelta ()) = ()
type instance ValDelta () = ()

instance Patchable () where
    patch () = ()
    changes () () = ()
    diffBundle () () = ()

instance PatchInstance () where
    -- This is what I'm spending my precious life on.
    () <^< () = ()

instance ValDeltaBundle () where
  bundleVD ((), ()) = ()
  unbundleVD () = ((),())
  valueBundle () = ()


-- | The default @ValDelta@ is just a product. Note that other
--   structures may have a different definition for @valDelta@.
data Jet a = Jet a (ILCDelta a)

deriving instance (Eq a, Eq (ILCDelta a)) => Eq (Jet a)
deriving instance (Show a, Show (ILCDelta a)) => Show (Jet a)


--
-- | Patchable tuples. In this case we just patch
--   each component independently, which may not be what
--   you want.
--
type instance ILCDelta (a,b) = (ILCDelta a, ILCDelta b)
type instance ValDelta (a,b) = (ValDelta a, ValDelta b)

instance (PatchInstance a, PatchInstance b) => PatchInstance (a,b) where
    (da,db) <^< (da',db') = (da <^< da', db <^< db')

instance (ValDeltaBundle a, ValDeltaBundle b) => ValDeltaBundle (a,b) where
    bundleVD ((a,b),(da,db)) = (bundleVD (a,da), bundleVD (b,db))
    unbundleVD (va, vb) = let (a,da) = unbundleVD va
                              (b, db) = unbundleVD vb
                          in
                              ((a,b),(da,db))
    valueBundle (a,b) = (valueBundle a, valueBundle b)

instance (Patchable a, Patchable b) => Patchable (a,b) where
    patch (va,vb) = (patch va, patch vb)
    changes (a0,b0) (a1,b1) = (changes a0 a1, changes b0 b1)
    diffBundle = undefined


--
-- | Patching for 'Maybe'
--
data MaybeDelta a =
      -- switch from something to a Just value. 
      MaybeJust a
      -- patch a Just value
    | MaybePatch (ILCDelta a)
      -- switch from something to a Nothing value.
    | MaybeNothing

data MaybeValDelta a =
      -- valdelta of a Just
      MaybeBundle (ValDelta a)
      -- switch between just and nothing values. Also used for Nothing to Nothing
    | MaybeReplace (Maybe a) (Maybe a)

type instance ILCDelta (Maybe a) = MaybeDelta a
type instance ValDelta (Maybe a) = MaybeValDelta a

instance (Show a, Show (ILCDelta a)) => Show (MaybeDelta a) where
  show (MaybeJust a) = "MaybeJust " ++ show a
  show (MaybePatch da) = "MaybePatch " ++ show da
  show (MaybeNothing)  = "MaybeNothing"
  
instance (Show a, Show (ValDelta a)) => Show (MaybeValDelta a) where
  show (MaybeBundle aa) = "MaybeBundle " ++ show aa
  show (MaybeReplace a a') = "MaybeReplace (" ++ show a ++ ") (" ++ show a' ++ ")"

-- | Note we define 'Maybe' as a sum type which can switch between 'Nothing' and @'Just' x@.
--   Another interpretation is that 'Nothing' means an empty patch or no changes. That interpretation
--   is NOT the one used here.  For the interpretation that Nothing means "no change" you should
--   use 'ReplaceOnly'.
--
instance (Patchable a) => Patchable (Maybe a) where
    patch (MaybeBundle va)    = Just (patch va)
    patch (MaybeReplace _ b)  = b

    diffBundle (Just x) (Just x') = MaybeBundle (diffBundle x x')
    diffBundle a        a'        = MaybeReplace a a'

instance (Patchable a, PatchInstance (ILCDelta a)) => PatchInstance (MaybeDelta a) where
    _             <^< MaybeNothing   = MaybeNothing
    _             <^< MaybeJust x    = MaybeJust x
    MaybeJust  x  <^< MaybePatch dx  = MaybeJust (patch $ bundleVD (x,dx))
    MaybePatch dx <^< MaybePatch dx' = MaybePatch (dx <^< dx')
    _             <^< _              = error "Mismatch for patch merge of Maybe"

instance (ValDeltaBundle a) => ValDeltaBundle (Maybe a) where
    bundleVD (x, MaybeNothing) = MaybeReplace x Nothing
    bundleVD (x, MaybeJust x') = MaybeReplace x (Just x')
    bundleVD (Just x, MaybePatch dx) = MaybeBundle (bundleVD (x,dx))
    bundleVD (_,_) = error "Mismatch in bundleVD for Maybe"

    unbundleVD (MaybeReplace x Nothing)       = (x, MaybeNothing)
    unbundleVD (MaybeReplace x (Just y))      = (x, MaybeJust y)
    unbundleVD (MaybeBundle xx) = let (x,dx) = unbundleVD xx
                                  in (Just x, MaybePatch dx)

    valueBundle (Just x) = MaybeBundle (valueBundle x)
    valueBundle Nothing  = MaybeReplace Nothing Nothing


--
-- Delta and ValDelta for Bool
--

data BoolVD =
      BoolChange Bool Bool
    | BoolSame Bool
    deriving (Eq, Show)

-- | There is no delta for raw 'Bool', you need to wrap it in 'ReplacableVal' to get
--   proper handling of sum types.
type instance ILCDelta Bool = Bool

-- | You should use 'ReplaceableVal (Bool a)' and it's ValDelta, not the raw 'Bool' type
type instance ValDelta Bool = BoolVD

-- | Patchable 'Bool' does nothing, wrap 'Bool' in 'ReplaceableVal' to get what you would
--   expect from a sum type.
instance Patchable Bool where
    patch (BoolSame x) = x
    patch (BoolChange _ x') = x'

    diffBundle x y
      | x == y     = BoolSame x
      | otherwise  = BoolChange x y
    

instance PatchInstance Bool where
    _ <^< y = y

instance ValDeltaBundle Bool where
    bundleVD (x,y) = diffBundle x y

    unbundleVD (BoolChange x y) = (x,y)
    unbundleVD (BoolSame x) = (x,x)

    valueBundle x = BoolSame x

--
-- | If a is a group, we can generate a Patchable type where the 
--   delta is the same type as the actual value.
--   Patches are performed using semigroup '(<>)'.
--   Works for some numbers (Integer) but for others you
--   have the problem that some values are unrepresentable.  For instance,
--   (changes a a') on float may produce a delta that is too small to
--   represent as a float.
--
--   We need @a@ to be a group since computing @changes@ requires the inverse of @a@
--

newtype SelfPatchable a = SelfPatchable a
    deriving (Eq, Show)

data SelfValDelta a = SelfValDelta a a

type instance ILCDelta (SelfPatchable a) = SelfPatchable a
type instance ValDelta (SelfPatchable a) = SelfValDelta a

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

instance (PatchInstance a) => PatchInstance (SelfPatchable a) where
    (SelfPatchable a) <^< (SelfPatchable b) = SelfPatchable (a <^< b)

instance (Monoid a) => ValDeltaBundle (SelfPatchable a) where
    bundleVD ((SelfPatchable a) , (SelfPatchable a')) = SelfValDelta a a'
    unbundleVD (SelfValDelta a a')                    = ((SelfPatchable a) , (SelfPatchable a'))
    valueBundle (SelfPatchable a)                     = SelfValDelta a mempty

instance (Group a, PatchInstance a) => Patchable (SelfPatchable a) where
    patch (SelfValDelta a da)                       = SelfPatchable (a <> da)
    changes (SelfPatchable a) (SelfPatchable b)     = SelfPatchable ((invert a) <> b)
    diffBundle (SelfPatchable a) (SelfPatchable a') = SelfValDelta a ((invert a) <> a')

instance (Ord a) => Ord (SelfPatchable a) where
    (SelfPatchable a) <= (SelfPatchable b) = a <= b

--
-- | Patchable generics, useful for records or extended sum types
--

type instance ILCDelta (K1 i x p) = K1 i (ILCDelta x) p
type instance ILCDelta ((:+:) x y p) = ((:+:) x y p)

class PatchableG i o where
  patchG :: i p -> o p -> i p
  changesG :: i p -> i p -> o p

instance (Patchable x, dx ~ ILCDelta x) => PatchableG (K1 a x) (K1 a dx) where
  patchG :: K1 a x p -> K1 a (ILCDelta x) p -> K1 a x p
  patchG (K1 x) (K1 dx) = K1 $ patch $ bundleVD (x,dx)
  changesG :: K1 a x p -> K1 a x p -> K1 a (ILCDelta x) p
  changesG (K1 x0) (K1 x1) = K1 $ changes x0 x1
  

instance (PatchableG i o, PatchableG i' o') => PatchableG (i :*: i') (o :*: o') where
  patchG (l0 :*: r0) (l1 :*: r1) = (patchG l0 l1) :*: (patchG r0 r1)
  changesG (l0 :*: r0) (l1 :*: r1) = (changesG l0 l1) :*: (changesG r0 r1)

--
-- patch for a sum type checks the value and delta. If they have the same tag
-- the patch is applied, otherwise it is ignored.
--

instance (PatchableG i o, PatchableG i' o') => PatchableG (i :+: i') (o :+: o') where
  patchG (L1 a) (L1 da) = L1 $ patchG a da
  patchG (L1 _a) (R1 _)  = error "Mismatched Sum type when attempting patch"
  patchG (R1 b) (R1 db) = R1 $ patchG b db
  patchG (R1 _b) (L1 _)  = error "Mismatched Sum type when attempting patch"
  
  changesG (L1 a) (L1 a') = L1 $ changesG a a'
  changesG (R1 b) (R1 b') = R1 $ changesG b b'
  changesG (L1 _a) (R1 _)  = error "Mismatched Sum type when attempting patch"
  changesG (R1 _b) (L1 _)  = error "Mismatched Sum type when attempting patch"

instance (PatchableG i o) => PatchableG (M1 _a _b i) (M1 _a' _b' o) where
  patchG   (M1 x) (M1 dx) = M1 $ patchG x dx
  changesG (M1 x) (M1 y)  = M1 $ changesG x y


instance PatchableG V1 V1 where
  patchG   = undefined
  changesG = undefined

instance PatchableG U1 U1 where
  patchG U1 U1   = U1
  changesG U1 U1 = U1


patchGeneric ::
  (Generic f,
   Generic (ILCDelta f),
   PatchableG (Rep f) (Rep (ILCDelta f)))
  => f -> (ILCDelta f) -> f
patchGeneric a da = to $ patchG (from a) (from da)

changesGeneric ::
  (Generic f,
   Generic (ILCDelta f),
   PatchableG (Rep f) (Rep (ILCDelta f)))
  => f -> f -> (ILCDelta f)
changesGeneric a b = to $ changesG (from a) (from b)  
  

--
-- PatchInstance for Generics
--

class PatchInstanceG i where
  combineG :: i p -> i p -> i p -- ^ generic version of '<^<'

instance (PatchInstance dx) => PatchInstanceG (K1 a dx) where
  combineG :: K1 a dx p -> K1 a dx p -> K1 a dx p
  combineG (K1 dx1) (K1 dx2) = K1 $ dx1 <^< dx2

instance (PatchInstanceG i, PatchInstanceG i') => PatchInstanceG (i :*: i') where
  combineG (l0 :*: r0) (l1 :*: r1) = (combineG l0 l1) :*: (combineG r0 r1)


instance (PatchInstanceG i, PatchInstanceG i') => PatchInstanceG (i :+: i') where
  combineG (L1 a0) (L1 a1) = L1 $ combineG a0 a1
  combineG (R1 b0) (R1 b1) = R1 $ combineG b0 b1
  combineG (L1 _) (R1 _)  = error "Mismatch when combining patches of a Sum Type"
  combineG (R1 _) (L1 _)  = error "Mismatch when combining patches of a Sum Type"



instance (PatchInstanceG i) => PatchInstanceG (M1 _a _b i) where
  combineG   (M1 x) (M1 dx) = M1 $ combineG x dx


-- can't combine void values
instance PatchInstanceG V1 where
  combineG = undefined

instance PatchInstanceG U1 where
  combineG U1 U1   = U1

combineGeneric :: (Generic v, PatchInstanceG (Rep v)) => v -> v -> v
combineGeneric a a' = to $ combineG (from a) (from a')


--
-- ValDelta for Generics
--
class ValDeltaBundleG v d o where
  bundleVDG :: (v :*: d) p -> o p
  unbundleVDG :: o p -> (v :*: d) p

instance (ValDeltaBundle x, dx ~ ILCDelta x, ValDelta x ~ o) => ValDeltaBundleG (K1 a x) (K1 a dx) (K1 a o) where
  bundleVDG (K1 x :*: K1 dx) = K1 $ bundleVD (x, dx)
  unbundleVDG (K1 v)         = let (x,dx) = unbundleVD v
                               in (K1 x) :*: (K1 dx)

instance (ValDeltaBundleG x dx o, 
          ValDeltaBundleG x' dx' o') => ValDeltaBundleG (x :*: x') (dx :*: dx') (o :*: o') where
  bundleVDG ((l0 :*: l1) :*: (dl0 :*: dl1)) = (bundleVDG (l0 :*: dl0)) :*: (bundleVDG (l1 :*: dl1))
  unbundleVDG (v :*: v')                    = let (x :*: dx) = unbundleVDG v
                                                  (x' :*: dx') = unbundleVDG v'
                                              in ((x :*: x') :*: (dx :*: dx'))

instance (ValDeltaBundleG x dx o, 
          ValDeltaBundleG x' dx' o') => ValDeltaBundleG (x :+: x') (dx :+: dx') (o :+: o') where
  bundleVDG ((L1 x) :*: (L1 dx)) = L1 $ bundleVDG (x :*: dx)
  bundleVDG ((R1 x) :*: (R1 dx)) = R1 $ bundleVDG (x :*: dx)
  bundleVDG ((L1 _) :*: (R1 _)) = error "Cannot bundle disjoint elements of a tagged union"
  bundleVDG ((R1 _) :*: (L1 _)) = error "Cannot bundle disjoint elements of a tagged union"

  unbundleVDG (L1 v) = let (x :*: dx) = unbundleVDG v
                       in (L1 x :*: L1 dx)
  unbundleVDG (R1 v) = let (x :*: dx) = unbundleVDG v
                       in (R1 x :*: R1 dx)

instance (ValDeltaBundleG v d o) => ValDeltaBundleG (M1 _a _b v) (M1 _a' _b' d) (M1 _x _y o) where
  bundleVDG ((M1 x) :*: (M1 dx)) = M1 $ bundleVDG (x :*: dx)
  unbundleVDG (M1 v) = let (x :*: dx) = unbundleVDG v
                       in ((M1 x) :*: (M1 dx))

bundleVDGeneric :: (Generic v, Generic d, Generic o,
                    (ValDeltaBundleG (Rep v) (Rep d) (Rep o))) => (v, d) -> o
bundleVDGeneric (v,d) = to $ bundleVDG ((from v) :*: (from d))

unbundleVDGeneric :: (Generic v, Generic d, Generic o,
                      (ValDeltaBundleG (Rep v) (Rep d) (Rep o))) => o -> (v,d)
unbundleVDGeneric o = let (v :*: dv) = unbundleVDG (from o)
                      in (to v,to dv)


