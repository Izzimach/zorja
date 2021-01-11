{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

module Zorja.Patchable
  ( 
    ILCDelta,
    ValDelta,

    Patchable,
    patch,
    changes,
    diffBundle,

    PatchInstance,
    mergePatches,
    (<^<),

    ValDeltaBundle,
    bundleVD,
    unbundleVD,
    valueBundle,
    valueUnbundle,
    deltaUnbundle,
    liftVD,
    lowerVD,
    valueLens,

    BoolVD (..),
    dIf,
    dThen,

    MaybeDelta (..),
    MaybeValDelta (..),

    DeltaRelation,
    FlipDeltaRelation,
    ValDeltaRelation,
    FlipValDeltaRelation
  )
where

import qualified GHC.Generics as GHC
import Generics.SOP
import Generics.SOP.NS


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
class PatchInstance a where
  (<^<) :: a -> a -> a

  default (<^<) :: (Generic a, All2 PatchInstance (Code a)) => a -> a -> a
  (<^<) = combineGeneric

-- | 'mergePatches' is a synonym for '(<^<)'
mergePatches :: (PatchInstance a) => a -> a -> a
mergePatches = (<^<)

-- | A @ValDelta@ is a value and it's delta bound together. Often this is
--   just a tuple '(a, ILCDelta a)' or the equivalent 'Jet1 a' but in some cases this may be some
--   other type for complicated or container types.
--   For example 'ValDelta [a]' might be '[(a, ILCDelta a)]' instead of '([a],[ILCDelta a])'
--   originally this type family was injective to help resolving recursive types but that may
--   not be required anymore.
type family ValDelta a = ja | ja -> a

class ValDeltaBundle a where
  bundleVD :: (a, ILCDelta a) -> ValDelta a

  default bundleVD ::
    ( Generic a,
      Generic (ILCDelta a),
      Generic (ValDelta a),
      All2 ValDeltaBundle (Code a),
      AllZip2 FlipDeltaRelation (Code (ILCDelta a)) (Code a),
      AllZip2 ValDeltaRelation (Code a) (Code (ValDelta a))
    ) =>
    (a, ILCDelta a) ->
    ValDelta a
  bundleVD = bundleVDGeneric

  unbundleVD :: ValDelta a -> (a, ILCDelta a)
  default unbundleVD ::
    ( Generic a,
      Generic (ILCDelta a),
      Generic (ValDelta a),
      All2 ValDeltaBundle (Code a),
      AllZip2 DeltaRelation (Code a) (Code (ILCDelta a)),
      AllZip2 FlipValDeltaRelation (Code (ValDelta a)) (Code a)
    ) =>
    ValDelta a ->
    (a, ILCDelta a)
  unbundleVD = unbundleVDGeneric

  -- | Given a value @a@ generates a @ValDelta a@ with a value of @a@
  --   and a no-op patch value. @patch (valueBundle x) = x@
  valueBundle :: a -> ValDelta a
  default valueBundle ::
    ( Generic a,
      Generic (ValDelta a),
      All2 ValDeltaBundle (Code a),
      AllZip2 ValDeltaRelation (Code a) (Code (ValDelta a))
    ) =>
    a ->
    ValDelta a
  valueBundle = valueBundleGeneric

valueUnbundle :: (ValDeltaBundle a) => ValDelta a -> a
valueUnbundle = fst . unbundleVD

deltaUnbundle :: (ValDeltaBundle a) => ValDelta a -> ILCDelta a
deltaUnbundle = snd . unbundleVD

-- | 'Patchable' is a typeclass for data that can be diff'd and patched.
--   The associated type @ILCDelta a@ must be a 'PatchInstance' since it
--   can be combined with other changes to generate a "combined patch"
--   and must support an empty patch. Note that even though 'PatchInstance'
--   is a 'Monoid' that combines small
--   patches into a single bigger patch, it may have different behavior than
--   some default 'Monoid' instance for that type. You may have to use a newtype
--   wrapper to distinguish the two.
--
--   @patch x (changes x x') = x'@
class (ValDeltaBundle a, PatchInstance (ILCDelta a)) => Patchable a where
  -- | @patch (bundleVD x dx)@ applies the changes in @dx@ to @x@ producing @x'@
  patch :: ValDelta a -> a

  default patch :: (Generic a, Generic (ValDelta a), All2 Patchable (Code a),
                    AllZip2 FlipValDeltaRelation (Code (ValDelta a)) (Code a)) => ValDelta a -> a
  patch = patchGeneric

  -- | @changes x x'@ generates a @dx :: ILCDelta a@ that can convert @x@ into @x'@ using @patch@
  --   Normally implemented in terms of 'diffBundle' but you can override with  your own if needed.
  changes :: a -> a -> ILCDelta a
  changes a a' = snd $ unbundleVD $ diffBundle a a'

  --default changes :: (Generic a, Generic (ILCDelta a), AllZip2 DeltaRelation (Code a) (Code (ILCDelta a)), All2 Patchable (Code a)) => a -> a -> ILCDelta a
  --changes a a' = changesGeneric a a'

  -- | Runs changes and bundles up the delta with the original value.
  --   Given two values @a@ and @a'@ then @aa = bundleChanges a a'@ means that
  --   @unbundle aa = (a, changes a a')@ and @patch aa = a'@
  diffBundle :: a -> a -> ValDelta a

  default diffBundle :: (Generic a, 
                         Generic (ValDelta a),
                         All2 Patchable (Code a), 
                         AllZip2 ValDeltaRelation (Code a) (Code (ValDelta a))) 
                        => a -> a -> ValDelta a
  diffBundle a a' = diffBundleGeneric a a'


-- | Given a function from 'a -> b' this will generate a function 'ValDelta a -> ValDelta b'
--   that applies the function to BOTH the original and patched value.
--   It won't be efficient but hopefully it will be correct.
--   If you want to modify the patched value while leaving the original intact, you can
--   use 'valueLens'
liftVD ::
  (Patchable a, Patchable b) =>
  (a -> b) ->
  (ValDelta a) ->
  (ValDelta b)
liftVD f = \vda ->
  let a = valueUnbundle vda
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
valueLens f vd =
  let a  = valueUnbundle vd
      a' = f (patch vd)
      bundleUp = \x -> diffBundle a x
   in fmap bundleUp a'

--
-- | The default @ValDelta@ is just a product. Note that other
--   structures may have a different definition for @valDelta@.
data Jet a = Jet a (ILCDelta a)

deriving instance (Eq a, Eq (ILCDelta a)) => Eq (Jet a)

deriving instance (Show a, Show (ILCDelta a)) => Show (Jet a)

--

--------------------------------------------------------
--
-- Patchable for haskell built-ins: (), tuple, Maybe, Bool
--
------------------------------------------------------


-- | Patching for ()
type instance ILCDelta () = ()

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
  unbundleVD () = ((), ())
  valueBundle () = ()

-- | Patchable tuples. In this case we just patch
--   each component independently, which may not be what
--   you want.
type instance ILCDelta (a, b) = (ILCDelta a, ILCDelta b)

type instance ValDelta (a, b) = (ValDelta a, ValDelta b)

instance (PatchInstance a, PatchInstance b) => PatchInstance (a, b) where
  (da, db) <^< (da', db') = (da <^< da', db <^< db')

instance (ValDeltaBundle a, ValDeltaBundle b) => ValDeltaBundle (a, b) where
  bundleVD ((a, b), (da, db)) = (bundleVD (a, da), bundleVD (b, db))
  unbundleVD (va, vb) =
    let (a, da) = unbundleVD va
        (b, db) = unbundleVD vb
     in ((a, b), (da, db))
  valueBundle (a, b) = (valueBundle a, valueBundle b)

instance (Patchable a, Patchable b) => Patchable (a, b) where
  patch (va, vb) = (patch va, patch vb)
  changes (a0, b0) (a1, b1) = (changes a0 a1, changes b0 b1)
  diffBundle = undefined



--
-- | Patching for 'Maybe'
data MaybeDelta a
  = -- switch from something to a Just value.
    MaybeJust a
  | -- patch a Just value
    MaybePatch (ILCDelta a)
  | -- switch from something to a Nothing value.
    MaybeNothing
  deriving (GHC.Generic)

data MaybeValDelta a
  = -- valdelta of a Just
    MaybeBundle (ValDelta a)
  | -- switch between just and nothing values. Also used for Nothing to Nothing
    MaybeReplace (Maybe a) (Maybe a)
  deriving (GHC.Generic)

type instance ILCDelta (Maybe a) = MaybeDelta a
type instance ValDelta (Maybe a) = MaybeValDelta a

instance DeltaRelation (Maybe a) (MaybeDelta a)
instance FlipDeltaRelation (MaybeDelta a) (Maybe a)
instance ValDeltaRelation (Maybe a) (MaybeValDelta a)
instance FlipValDeltaRelation (MaybeValDelta a) (Maybe a)

instance (Show a, Show (ILCDelta a)) => Show (MaybeDelta a) where
  show (MaybeJust a) = "MaybeJust " ++ show a
  show (MaybePatch da) = "MaybePatch " ++ show da
  show (MaybeNothing) = "MaybeNothing"

instance (Show a, Show (ValDelta a)) => Show (MaybeValDelta a) where
  show (MaybeBundle aa) = "MaybeBundle " ++ show aa
  show (MaybeReplace a a') = "MaybeReplace (" ++ show a ++ ") (" ++ show a' ++ ")"

-- | Note we define 'Maybe' as a sum type which can switch between 'Nothing' and @'Just' x@.
--   Another interpretation is that 'Nothing' means an empty patch or no changes. That interpretation
--   is NOT the one used here.  For the interpretation where Nothing means "no change" you should
--   use 'ReplaceOnly'.
instance (Patchable a) => Patchable (Maybe a) where
  patch (MaybeBundle va) = Just (patch va)
  patch (MaybeReplace _ b) = b

  diffBundle (Just x) (Just x') = MaybeBundle (diffBundle x x')
  diffBundle a a' = MaybeReplace a a'

instance (Patchable a, PatchInstance (ILCDelta a)) => PatchInstance (MaybeDelta a) where
  _ <^< MaybeNothing = MaybeNothing
  _ <^< MaybeJust x = MaybeJust x
  MaybeJust x <^< MaybePatch dx = MaybeJust (patch $ bundleVD (x, dx))
  MaybePatch dx <^< MaybePatch dx' = MaybePatch (dx <^< dx')
  _ <^< _ = error "Mismatch for patch merge of Maybe"

instance (ValDeltaBundle a) => ValDeltaBundle (Maybe a) where
  bundleVD (x, MaybeNothing) = MaybeReplace x Nothing
  bundleVD (x, MaybeJust x') = MaybeReplace x (Just x')
  bundleVD (Just x, MaybePatch dx) = MaybeBundle (bundleVD (x, dx))
  bundleVD (_, _) = error "Mismatch in bundleVD for Maybe"

  unbundleVD (MaybeReplace x Nothing) = (x, MaybeNothing)
  unbundleVD (MaybeReplace x (Just y)) = (x, MaybeJust y)
  unbundleVD (MaybeBundle xx) =
    let (x, dx) = unbundleVD xx
     in (Just x, MaybePatch dx)

  valueBundle (Just x) = MaybeBundle (valueBundle x)
  valueBundle Nothing = MaybeReplace Nothing Nothing

--
-- Delta and ValDelta for Bool
--

data BoolVD
  = BoolChange Bool Bool
  | BoolSame Bool
  deriving (Eq, Show, GHC.Generic)

instance Generic BoolVD

type instance ILCDelta Bool = Bool
type instance ValDelta Bool = BoolVD

instance DeltaRelation Bool Bool
instance FlipDeltaRelation Bool Bool
instance ValDeltaRelation Bool BoolVD
instance FlipValDeltaRelation BoolVD Bool


-- | Patchable 'Bool' does nothing, wrap 'Bool' in 'ReplaceableVal' to get what you would
--   expect from a sum type.
instance Patchable Bool where
  patch (BoolSame x) = x
  patch (BoolChange _ x') = x'

  diffBundle x y
    | x == y = BoolSame x
    | otherwise = BoolChange x y

instance PatchInstance Bool where
  _ <^< y = y

instance ValDeltaBundle Bool where
  bundleVD (x, y) = diffBundle x y

  unbundleVD (BoolChange x y) = (x, y)
  unbundleVD (BoolSame x) = (x, x)

  valueBundle x = BoolSame x


-- | Generate a ValDelta-ish version of an if statement.
dIf :: (Patchable a) => (a -> Bool) -> (ValDelta a -> BoolVD)
dIf p = \aa -> let t = p (valueUnbundle aa)
                   t' = p (patch aa)
               in diffBundle t t'

dThen :: (Patchable b) => (Bool -> b) -> (BoolVD -> ValDelta b)
dThen p (BoolChange t t') = diffBundle (p t) (p t')
dThen p (BoolSame t)      = valueBundle (p t)
                     






--
-- ValDelta for Generics via the SOP Generic encoding
--

--
-- we need to apply 'ILCDelta' and 'ValDelta' to the encodings use by SOP
--

newtype Del a = Del {unDel :: ILCDelta a}
newtype VDel a = VDel {unVDel :: ValDelta a}

type instance ILCDelta (I a) = Del a
type instance ValDelta (I a) = VDel a



class (b ~ (ILCDelta a)) => DeltaRelation a b
class (a ~ (ILCDelta b)) => FlipDeltaRelation a b
class (b ~ (ValDelta a)) => ValDeltaRelation a b
class (a ~ (ValDelta b)) => FlipValDeltaRelation a b


--
-- Functions to transform SOP data  between difference ILC datatypes.
-- For instance sometimes we have a SOP of 'ILCDelta v' which shows up
-- as 'SOP I (Code (ILCDelta v))' but we really want it represented
-- with a 'Del' since that's how all the functions are specified later on.
-- so we need to convert from 'SOP I (Code (ILCDelta v))' to 'SOP Del (Code v)'
-- which is the function 'toDel' below. The constraint 'FlipDeltaRelation' is
-- a typeclass representation of 'b ~ ILCDelta a' which is used to guarantee all
-- parts of the datatype satisfy this constraint.

iDel :: forall a b. (FlipDeltaRelation a b) => I a -> Del b
iDel (I da) = Del da

iunDel :: forall a b. (DeltaRelation a b) => Del a -> I b
iunDel (Del da) = I da

iValDel :: forall a b. (FlipValDeltaRelation a b) => I a -> VDel b
iValDel (I aa) = VDel aa

iunValDel :: forall a b. (ValDeltaRelation a b) => VDel a -> I b
iunValDel (VDel aa) = I aa

toDel :: (AllZipN (Prod SOP) FlipDeltaRelation xs ys) => SOP I xs -> SOP Del ys
toDel dv = htrans (Proxy :: Proxy FlipDeltaRelation) iDel dv

fromDel :: (AllZipN (Prod SOP) DeltaRelation xs ys) => SOP Del xs -> SOP I ys
fromDel dv = htrans (Proxy :: Proxy DeltaRelation) iunDel dv

toVDel :: (AllZipN (Prod SOP) FlipValDeltaRelation xs ys) => SOP I xs -> SOP VDel ys
toVDel vv = htrans (Proxy :: Proxy FlipValDeltaRelation) iValDel vv

fromVDel :: (AllZipN (Prod SOP) ValDeltaRelation xs ys) => SOP VDel xs -> SOP I ys
fromVDel r = htrans (Proxy :: Proxy ValDeltaRelation) iunValDel  r

bundleVDGeneric ::
  ( Generic v,
    Generic (ILCDelta v),
    Generic (ValDelta v),
    All2 ValDeltaBundle (Code v),
    AllZip2 FlipDeltaRelation (Code (ILCDelta v)) (Code v),
    AllZip2 ValDeltaRelation (Code v) (Code (ValDelta v))
  ) =>
  (v, ILCDelta v) ->
  ValDelta v
bundleVDGeneric (a, d) = to $ fromVDel $ bundleVDG (from a) (toDel $ from d)

bundleVDG :: (All2 ValDeltaBundle xs) => SOP I xs -> SOP Del xs -> SOP VDel xs
bundleVDG (SOP a) (SOP da) = SOP $ bundleSumG a da

bundleSumG :: (All2 ValDeltaBundle xs) => NS (NP I) xs -> NS (NP Del) xs -> NS (NP VDel) xs
bundleSumG (Z a) (Z da) = Z $ bundleProductG a da
bundleSumG (S xs) (S dxs) = S $ bundleSumG xs dxs
bundleSumG _ _ = error "Mismatch of sum type in Generic bundleVD"

bundleProductG :: (All ValDeltaBundle xs) => NP I xs -> NP Del xs -> NP VDel xs
bundleProductG Nil Nil = Nil
bundleProductG (I x :* xs) (Del dx :* dxs) = VDel (bundleVD (x, dx)) :* bundleProductG xs dxs

unbundleVDGeneric ::
  ( Generic v,
    Generic (ILCDelta v),
    Generic (ValDelta v),
    All2 ValDeltaBundle (Code v),
    AllZip2 DeltaRelation (Code v) (Code (ILCDelta v)),
    AllZip2 FlipValDeltaRelation (Code (ValDelta v)) (Code v)
  ) =>
  ValDelta v ->
  (v, ILCDelta v)
unbundleVDGeneric o =
  let (r, dr) = unBundleVDG $ toVDel $ from o
  in (to r, to $ fromDel dr)

unBundleVDG :: (All2 ValDeltaBundle xs) => SOP VDel xs -> (SOP I xs, SOP Del xs)
unBundleVDG (SOP aa) =
  let (r, dr) = unBundleSumG aa
   in (SOP r, SOP dr)

unBundleSumG :: (All2 ValDeltaBundle xs) => NS (NP VDel) xs -> (NS (NP I) xs, NS (NP Del) xs)
unBundleSumG (Z a) =
  let (r, dr) = unBundleProductG a
   in (Z r, Z dr)
unBundleSumG (S xs) =
  let (r, dr) = unBundleSumG xs
   in (S r, S dr)

unBundleProductG :: (All ValDeltaBundle xs) => NP VDel xs -> (NP I xs, NP Del xs)
unBundleProductG Nil = (Nil, Nil)
unBundleProductG (VDel x :* xs) =
  let (rs, drs) = unBundleProductG xs
      (r, dr) = unbundleVD x
   in (I r :* rs, Del dr :* drs)

valueBundleGeneric ::
  ( Generic a,
    Generic (ValDelta a),
    All2 ValDeltaBundle (Code a),
    AllZip2 ValDeltaRelation (Code a) (Code (ValDelta a))
  ) =>
  a ->
  ValDelta a
valueBundleGeneric a = to $ fromVDel $ valueBundleSOP (from a)

valueBundleFn :: (ValDeltaBundle a) => (I -.-> VDel) a
valueBundleFn = Fn (\(I a) -> VDel (valueBundle a))

valueBundleSOP :: (All2 ValDeltaBundle xs) => SOP I xs -> SOP VDel xs
valueBundleSOP s = ap_SOP valueBundleMembers s
  where
    valueBundleMembers = hcpure (Proxy :: Proxy ValDeltaBundle) valueBundleFn



patchGeneric ::
  ( Generic a,
    Generic (ValDelta a),
    All2 Patchable (Code a),
    AllZip2 FlipValDeltaRelation (Code (ValDelta a)) (Code a)
  ) => ValDelta a -> a
patchGeneric aa = to $ patchSOP (toVDel $ from aa)

-- | 'patch' lifted into SOP space
patchFn :: (Patchable a) => (VDel -.-> I) a
patchFn = Fn (\(VDel aa) -> I (patch aa))

patchSOP :: (All2 Patchable xs) => SOP VDel xs -> SOP I xs
patchSOP s = ap_SOP patchMembers s
  where
    patchMembers = hcpure (Proxy :: Proxy Patchable) patchFn

diffBundleGeneric ::
  ( Generic a,
    Generic (ValDelta a),
    All2 Patchable (Code a),
    AllZip2 ValDeltaRelation (Code a) (Code (ValDelta a))
  ) => a -> a -> (ValDelta a)
diffBundleGeneric a b = to $ fromVDel $ diffBundleG (from a) (from b)

diffBundleG :: (All2 Patchable xs) => SOP I xs -> SOP I xs -> SOP VDel xs
diffBundleG (SOP a) (SOP a') = SOP (diffBundleSumG a a')

diffBundleSumG :: (All2 Patchable xs) => NS (NP I) xs -> NS (NP I) xs -> NS (NP VDel) xs
diffBundleSumG (Z a) (Z da) = Z $ diffBundleProductG a da
diffBundleSumG (S xs) (S dxs) = S $ diffBundleSumG xs dxs
diffBundleSumG _ _ = error "Mismatch of sum type in Generic changes"

diffBundleProductG :: (All Patchable xs) => NP I xs -> NP I xs -> NP VDel xs
diffBundleProductG Nil Nil = Nil
diffBundleProductG (I a :* as) (I a' :* as') = VDel (diffBundle a a') :* diffBundleProductG as as'


--
-- PatchInstance for Generics
--

combineGeneric :: (Generic a,
                   All2 PatchInstance (Code a)) => a -> a -> a
combineGeneric a a' = to $ combineG (from a) (from a')

combineG :: (All2 PatchInstance xs) => SOP I xs -> SOP I xs -> SOP I xs
combineG (SOP da) (SOP da') = SOP (combineSumG da da')

combineSumG :: (All2 PatchInstance xs) => NS (NP I) xs -> NS (NP I) xs -> NS (NP I) xs
combineSumG (Z da) (Z da') = Z $ combineProductG da da'
combineSumG (S da) (S da') = S $ combineSumG da da'
combineSumG _ _ = error "Mismatch of sum types in generic combine"

combineProductG :: (All PatchInstance xs) => NP I xs -> NP I xs -> NP I xs
combineProductG Nil Nil = Nil
combineProductG (I da :* das) (I da' :* das') = I (da <^< da') :* combineProductG das das'
