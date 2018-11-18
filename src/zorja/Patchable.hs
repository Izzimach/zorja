{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Zorja.Patchable where

--
--
--

class (Semigroup (Change a)) => Patchable a where
  type Change a
  patch :: a -> Change a -> a
  -- @patch a (diff a b) = b@
  diff ::  a -> a -> Change a
