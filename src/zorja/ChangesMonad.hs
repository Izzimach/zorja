{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Zorja.ChangesMonad where

--import Data.Semigroup
--import Data.Monoid

import Control.Monad.State

import Zorja.Patchable

--
-- State monad for a Patchable data type, using @changes@ to find change
-- values. Any time a put is performed, the new state
-- is compare to the old state and changes are recorded. This allows the
-- use of lenses that don't work on @PatchedJet@ but is inefficient.
-- For more effecient generation of changes you can generate lenses that
-- work on the @PatchedJet@ datatype and then use a @StateT@ monad that
-- takes a @PatchedJet s@ instead of @s@ as the monad state.
--

data ChangesMonad s m a = ChangesMonad { runCM :: (PatchedJet s) -> m (a, PatchedJet s) }

instance (Functor m) => Functor (ChangesMonad s m) where
  fmap f pm = ChangesMonad (\pj -> let mapfst = \(a,b) -> (f a, b)
                                   in fmap mapfst (runCM pm pj))
                    
instance (Applicative m) => Applicative (ChangesMonad s m) where
  pure a = ChangesMonad (\pj -> pure (a, pj))
  x <*> y = ChangesMonad
    (\pj -> let x' = runCM x pj
                y' = runCM y pj
                fm (f,_) = \(a,s) -> (f a, s)
            in (fmap fm x') <*> y')
  
instance (Monad m) => Monad (ChangesMonad s m) where
  return    = pure
  a >>= b   = ChangesMonad (\pj -> do (a1,pj1) <- runCM a pj
                                      runCM (b a1) pj1)

instance (Monad m, Patchable s) => MonadState s (ChangesMonad s m) where
  get = ChangesMonad (\pj -> return (patchedval pj, pj))
  --
  -- in the function @s@ is the new state sent by put, and pj is the
  -- current state from the upstream monad.
  put = (\s -> ChangesMonad
          (\pj -> let newhistory = history pj <> changes (patchedval pj) s
                      newpj = PatchedJet s newhistory
                  in return ((), newpj)))

