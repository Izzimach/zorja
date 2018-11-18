{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Main where

import Data.Constraint
import Data.Semigroup hiding (diff)

import Control.Applicative

import Control.Lens
import Control.Lens.Tuple
import Control.Monad.State

class (Semigroup (Change a)) => Patchable a where
  type Change a
  patch :: a -> Change a -> a
  -- @patch a (diff a b) = b@
  diff ::  a -> a -> Change a

data Jet a = Jet
  {
    position :: a, 
    velocity :: Change a
  }

jetChange :: (Patchable a, Semigroup (Change a)) => Jet a -> (a -> Change a) -> Jet a
jetChange (Jet a da) f = let da' = f a
                      in
                        Jet (patch a da') (da <> da')

jetify :: (Patchable a, Monoid (Change a)) => a -> Jet a
jetify x = Jet { position = x, velocity = mempty } 

showJet :: (Show a, Show (Change a)) => Jet a -> String
showJet a = let x = position a
                dx = velocity a
            in "Jet " ++ show x ++ ", " ++ show dx

instance (Show a, Show (Change a)) => Show (Jet a) where
  show x = showJet x



--
-- Atomic Jet types are primitives where the "diff"
-- is simply replacing the previous value with a whole
-- new value. No incremental relationship is assumed between
-- the old and new values. The diff type is called
-- "Wham" and behaves as an (Option (Last x))

newtype AtomicJet a = Atomic a deriving (Eq, Show)

atomicWham :: (a -> b) -> AtomicJet a -> Wham b
atomicWham f (Atomic a) = Wham (f a)

data Wham a = NoWham 
            | Wham a
  deriving (Eq, Show)

instance Functor Wham where
  fmap f (Wham a) = Wham (f a)

instance Semigroup (Wham a) where
  a <> (Wham b) = Wham b
  a <> NoWham = a

instance Monoid (Wham a) where
  mempty = NoWham
  mappend = (<>)


-- note that the Change is (Wham a) and not (Wham (Change a)) because
-- we don't know if there is (Patchable a) and in any case we
-- just replace the whole a every time anyway, instead of incrementally
-- modifying it

instance (Eq a) => Patchable (AtomicJet a) where
  type Change (AtomicJet a) = Wham a
  patch :: AtomicJet a -> Wham a -> AtomicJet a
  patch a ad =  case ad of
                  NoWham -> a
                  Wham b  -> Atomic b

  diff :: AtomicJet a -> AtomicJet a -> Wham a
  diff (Atomic x) (Atomic y) =  if x == y
                                  then NoWham
                                  else (Wham y)

instance Functor AtomicJet where
  fmap f (Atomic a) = Atomic (f a)


instance (Patchable a, Patchable b) => Patchable (a,b) where
  type Change (a,b) = (Change a, Change b)
  patch :: (a,b) -> (Change a,Change b) -> (a,b)
  patch (a,b) (da,db) = (patch a da, patch b db)

  diff :: (a,b) -> (a,b) -> (Change a, Change b)
  diff (a0,b0) (a1,b1) = (diff a0 a1, diff b0 b1)


-- A PatchedJet contains patch data and the value AFTER the
-- patch has been applied. This is useful when compose functions
-- that produce and accumulate patch data. Otherwise when composing
-- we have to always apply 'patch a da' to get the most up-to-date
-- changed value.

data PatchedJet a = PatchedJet { val :: a, history :: Change a }

deriving instance (Eq a, Eq (Change a), Patchable a) => Eq (PatchedJet a)
deriving instance (Show a, Show (Change a), Patchable a) => Show (PatchedJet a)

toPatchedJet :: (Patchable a, Monoid (Change a)) => a -> PatchedJet a
toPatchedJet a = PatchedJet a mempty

instance (Patchable a, Patchable b, Semigroup (Change a), Semigroup (Change b)) =>
  Field1 (PatchedJet (a,b)) (PatchedJet (a,b)) (PatchedJet a) (PatchedJet a)
    where
  _1 k (PatchedJet x@(a,b) dx@(da,db)) = 
    let x' = k (PatchedJet a da)
        lxify = \(PatchedJet a' da') -> PatchedJet (a',b) (da', db)
    in fmap lxify x'
  

instance (Patchable a, Patchable b, Semigroup (Change a), Semigroup (Change b)) =>
  Field2 (PatchedJet (a,b)) (PatchedJet (a,b)) (PatchedJet b) (PatchedJet b)
    where
  _2 k (PatchedJet x@(a,b) dx@(da,db)) = 
    let b' = k (PatchedJet b db)
        lxify = \(PatchedJet b' db') -> PatchedJet (a,b') (da, db')
    in fmap lxify b'

  

pjetGo :: (Patchable a) => a -> (a -> Change a) -> PatchedJet a
pjetGo a f = PatchedJet a (f a)

pjetLens :: (Patchable a, Semigroup (Change a)) => 
  (a -> Change a) -> PatchedJet a -> PatchedJet a
pjetLens f (PatchedJet a da) = let da' = f a
                               in PatchedJet (patch a da') (da <> da')

jetWhamLens :: (a -> a) -> PatchedJet (AtomicJet a) -> PatchedJet (AtomicJet a)
jetWhamLens f (PatchedJet (Atomic a) _) =
  let a' = f a
  in PatchedJet (Atomic a') (Wham a')


--
-- monadic lens operations
--

data PatchedMonad s m a = PM { runPM :: (PatchedJet s) -> m (a, PatchedJet s) }

instance (Functor m) => Functor (PatchedMonad s m) where
  fmap f pm = PM (\pj -> let mapfst = \(a,b) -> (f a, b)
                         in fmap mapfst (runPM pm pj))
                    
instance (Applicative m) => Applicative (PatchedMonad s m) where
  pure a = PM (\pj -> pure (a, pj))
  x <*> y = PM
    (\pj -> let x' = runPM x pj
                y' = runPM y pj
                fm (f,s) = \(a,s) -> (f a, s)
            in (fmap fm x') <*> y')
  
instance (Monad m) => Monad (PatchedMonad s m) where
  return    = pure
  a >>= b   = PM (\pj -> do (a1,pj1) <- runPM a pj
                            runPM (b a1) pj1)

instance (Monad m, Patchable s) => MonadState s (PatchedMonad s m) where
  get = PM (\pj -> return (val pj, pj))
  put = (\s -> PM (\pj -> let newhistory = history pj <> diff (val pj) s
                              newpj = PatchedJet s newhistory
                          in return ((), newpj)))


--
--
--


instance Patchable Int where
  type Change Int = Option (Last Int)
  patch a da = case getOption da of
                 Nothing -> a
                 Just (Last a') -> a'
  diff a b = if (a == b)
             then Option Nothing
             else Option $ Just (Last b)

instance Patchable String where
  type Change String = Option (Last String)
  patch a da = case getOption da of
                 Nothing -> a
                 Just (Last a') -> a'
  diff a b = if (a == b)
             then Option Nothing
             else Option (Just (Last b))

data SomeDude = SD { v1 :: Int, v2 :: String } deriving (Eq, Show)
data SomeDudeD = SDD { v1d :: Change Int, v2d :: Change String } deriving (Eq, Show)


instance Semigroup SomeDudeD where
  a <> b = SDD (v1d a <> v1d b) (v2d a <> v2d b)

instance Monoid SomeDudeD where
  mempty = SDD mempty mempty

instance Patchable SomeDude where
  type Change SomeDude = SomeDudeD
  patch a da = let v1' = patch (v1 a) (v1d da)
                   v2' = patch (v2 a) (v2d da)
               in SD v1' v2'
  diff a b = let v1d' = diff (v1 a) (v1 b)
                 v2d' = diff (v2 a) (v2 b)
             in SDD v1d' v2d'
  
v1lens :: Lens' SomeDude Int
v1lens = lens v1 (\somedude newv -> somedude { v1 = newv})


pjlens :: Lens' (PatchedJet SomeDude) SomeDude
pjlens = lens val (\pj newval -> let vald = diff (val pj) newval
                                     mergedhistory = (history pj) <> vald
                                 in PatchedJet newval mergedhistory)

v2lens :: Lens' SomeDude String
v2lens = lens v2 (\somedude newv -> somedude { v2 = newv})


incDude :: State SomeDude ()
incDude = do
  v1lens .= 2
  v2lens %= ("blargh " ++)
  return ()

incDudePatch :: PatchedMonad SomeDude Identity ()
incDudePatch = do
  v2lens %= ("blargh" ++)
  return ()

incDudePatch2 :: PatchedMonad SomeDude Identity ()
incDudePatch2 = do
  v1lens .= 2
  return ()

startDudeValue = SD 3 "argh"

val1 = snd . runIdentity $ runPM incDudePatch (toPatchedJet startDudeValue)
val2 = snd . runIdentity $ runPM incDudePatch2 (toPatchedJet startDudeValue)

main :: IO ()
main = do
  let x = jetify (Atomic (3 :: Integer))
  putStrLn (showJet x)
  let a = jetify (Atomic (2 :: Int),Atomic "argh")
  putStrLn (showJet a)
  let b = PatchedJet (Atomic 2,Atomic 3) (mempty :: (Wham Int, Wham Int))
  let c = over _2 (jetWhamLens ((-) 3)) $ over _1 (jetWhamLens (+2)) b
  putStrLn $ show b
  putStrLn $ show c
  let d = view _1 b
  putStrLn $ show d
  
