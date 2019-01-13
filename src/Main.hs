{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import GHC.Generics

import Data.Text as T
import Data.Semigroup hiding (diff, All)

import Data.Kind (Constraint, Type)

--import Control.Applicative

import Control.Lens hiding (from, to)
--import Control.Lens.Tuple
import Control.Monad.State

import Zorja.Patchable


data HKDDelta a

--
-- A trick to remove Identity in higher-kinded types
--

type family HKD f a where
  HKD Identity a = a
  HKD HKDDelta a = PatchDelta a
  HKD f a        = f a


--
-- Some record. We want to record changes to this record
-- (performed using lenses) incrementally.
--

data SomeDude f = SD
  {
    v1 :: HKD f (Pair (Sum Int)),
    v2 :: HKD f (Text)
  } deriving (Generic)

type instance PatchDelta (SomeDude Identity) = SomeDude HKDDelta

--
-- default type is SomeDude Identity, the diff type is SomeDude HKDDelta
--

deriving instance Show (SomeDude Identity)
deriving instance Show (SomeDude HKDDelta)


instance Semigroup (SomeDude HKDDelta) where
  (SD f1 f2) <> (SD f1' f2') = SD (f1 <> f1') (f2 <> f2')

instance Monoid (SomeDude HKDDelta) where
  mempty = SD mempty mempty
  mappend = (<>)

instance Patchable (SomeDude Identity) where
  patch s ds = patchGeneric s ds
  changes s1 s2 = changesGeneric s1 s2


--
-- encode example from GHC.Generics
--

class Encode' f where
  encode' :: f p -> [Bool]

instance Encode' V1 where
  encode' _ = undefined

instance Encode' U1 where
  encode' U1 = []

instance (Encode' f, Encode' g) => Encode' (f :+: g) where
  encode' (L1 x) = False : encode' x
  encode' (R1 x) = True  : encode' x

instance (Encode' f, Encode' g) => Encode' (f :*: g) where
  encode' (x :*: y) = encode' x ++ encode' y

instance (Encode c) => Encode' (K1 i c) where
  encode' (K1 x) = encode x

instance (Encode' f) => Encode' (M1 D t f) where
  encode' (M1 x) = encode' x
instance (Encode' f, Constructor t) => Encode' (M1 C t f) where
  encode' mx@(M1 x) = if conName mx == "PatchedJet"
                      then True : encode' x
                      else False : encode' x
instance (Encode' f) => Encode' (M1 S t f) where
  encode' (M1 x) = encode' x

class Encode a where
  encode :: a -> [Bool]
  default encode :: (Generic a, Encode' (Rep a)) => a -> [Bool]
  encode x = encode' (from x)

instance Encode Text where
  encode _ = [True]

instance Encode Integer where
  encode _ = [True]

instance (Encode a) => Encode (Option a) where
  encode a = True : (encode $ getOption a)

instance (Encode a) => Encode (Maybe a) where
  encode Nothing = [False]
  encode (Just a) = True : (encode a)

instance Encode (Last a) where
  encode _ = [True]
  
instance Encode Int where
  encode _ = [True]

instance Encode ((,) a b) where
  encode _ = [True, True]

instance Encode (Pair a) where
  encode (Ax _ _) = [True,True]
  
instance Encode (SomeDude Identity)
instance Encode (SomeDude HKDDelta)
instance (Encode a, Encode (PatchDelta a)) => Encode (PatchedJet a)

--
-- lens via generics
--

data LensFor s a = LensFor
  { getLensFor :: Lens' s a }

class GLenses z i o where
  glenses :: Lens' (z Identity) (i p) -> o p


--
-- convert from @a@ to a lens from @(z Identity)@ to @a@
--

instance GLenses z (K1 _x a)
                   (K1 _x (LensFor (z Identity) a)) where
  glenses l = K1
              $ LensFor
              $ \f -> l $ fmap K1 . f . unK1
  {-# INLINE glenses #-}

instance (GLenses z i o) => GLenses z (M1 _a _b i) (M1 _a _b o) where
  glenses l = M1 $ glenses $ \f -> l $ fmap M1 . f . unM1
  {-# INLINE glenses #-}

instance (GLenses z i o, GLenses z i' o') => GLenses z (i :*: i') (o :*: o') where
  glenses l = glenses (\f -> l (\(a :*: b) -> fmap (:*: b) $ f a))
          :*: glenses (\f -> l (\(a :*: b) -> fmap (a :*:) $ f b))
  {-# INLINE glenses #-}

instance GLenses z V1 V1 where
  glenses _ = undefined

instance GLenses z U1 U1 where
  glenses _ = U1


getLenses :: forall z.
  ( Generic (z Identity),
    Generic (z (LensFor (z Identity))),
    GLenses z (Rep (z Identity)) (Rep (z (LensFor (z Identity)))))
          => z (LensFor (z Identity))
getLenses = to $ glenses @z $ iso from to


--
-- SomeDude rec
-- 


startDudeValue :: SomeDude Identity
startDudeValue = SD {
  v1 = Ax 3 3,
  v2 = (pack "argh")
  }

processDudeValue :: StateT (SomeDude Identity) IO (SomeDude Identity)
processDudeValue = do
  let SD (LensFor lv1) (LensFor _lv2) = getLenses
  lv1 .= (Ax 4 5)
  get >>= return

--  (SD { v1 = Ax 5 3, v2 = (pack "argh")})

main :: IO ()
main = do
  let x = toJet (AtomicLast (3 :: Integer))
  putStrLn $ show x
  dd <- evalStateT processDudeValue startDudeValue
  putStrLn $ show dd
  

  

--
-- transient workspace
--

type family All (c :: Type -> Constraint) (ts :: [Type]) :: Constraint where
  All c '[]     = ()
  All c (t ': ts) = (c t, All c ts)


data HList (ts :: [Type]) where
  HNil :: HList '[]
  (:#) :: t -> HList ts -> HList (t ': ts)

infixr 5 :#

hLength :: HList ts -> Int
hLength HNil = 0
hLength (_ :# ts) = 1 + hLength ts


instance (All Eq ts) => Eq (HList ts) where
  HNil == HNil = True
  (a :# as) == (b :# bs)        =   a == b && as == bs                                              
instance (All Eq ts, All Ord ts) => Ord (HList ts) where
  compare HNil HNil = EQ
  compare (a :# as) (b :# bs)   =
    case (compare a b) of
      EQ         -> compare as bs
      e          -> e


instance (All Show ts) => Show (HList ts) where
  show HNil = "Nil"
  show (x :# xs) = show x ++ " :# " ++ show xs
                                    

type family AllEq (ts :: [Type]) :: Constraint where
  AllEq '[] = ()
  AllEq (t ': ts) = (Eq t, AllEq ts)

newtype Cont a = Cont
          { runCont :: forall r . (a -> r) -> r }

instance Functor Cont where
  fmap fab (Cont far) = Cont $ \fbr -> far (fbr . fab)

instance Applicative Cont where
  pure a = Cont $ \far -> far a
  (Cont fabrr) <*> (Cont far) = Cont $ \fbr -> let fabr = \fab -> far (fbr . fab)
                                               in fabrr fabr

instance Monad Cont where
  return = pure
  (Cont l) >>= r = Cont $ \fbr -> let far  = \a -> runCont (r a) fbr
                                  in l far

newtype ContT (m :: * -> *) a = ContT { runContT :: forall r. (a -> m r) -> m r }

instance Functor (ContT m) where
  fmap fab c = ContT $ \fbmr -> let famr = runContT c
                                in famr (fbmr . fab)

instance Applicative (ContT m) where
  pure a = ContT $ \fmar -> fmar a
  fabmrmr <*> amr = ContT $ \bmr -> let fabmr = \fab -> (runContT amr) (bmr . fab)
                                    in (runContT fabmrmr) fabmr

instance Monad (ContT m) where
  return = pure
  (ContT l) >>= r = ContT $ \fbmr -> let amr = \a -> runContT (r a) fbmr
                                     in l amr
             


