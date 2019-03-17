{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Zorja.ZHOAS where

import Data.Kind (Constraint)

import Zorja.Patchable


--
-- Code in here is used for expressing your function as
-- a DSL, specifically HOAS (Higher-Order Abstrac Syntax).
-- This HOAS function can then be interpreted as a simple
-- function from a -> b. Alternately the DSL can be
-- interpreted as a function (a -> b) along with the "derivative"
-- a -> (Delta a) -> (Delta b).
--
-- For reference see [Cai, Giarrusso, Rendel, Ostermann]
--   "A theory of changes for higher-order languages incrementalizing 
--    lambda-calculi by static differentiation."
-- also [Elliott] "Compiling to Categories"
-- and finally Phil Freeman's blog "Incrementally Improving the DOM"
--

class ZHOAS rep where
  type ZOk rep a :: Constraint
  lam :: (ZOk rep a, ZOk rep b, ZOk rep (a -> b)) => (rep a -> rep b) -> rep (a -> b)
  app :: (ZOk rep a, ZOk rep b, ZOk rep (a -> b)) => rep (a -> b) -> rep a -> rep b
  zlift :: (ZOk rep a) => a -> rep a


--
-- The type ZE lets you eval a ZHOAS expression as a simple value or function a -> b
--

newtype ZE a = ZE { unZE :: a }

evalZE :: ZE a -> a
evalZE = unZE

instance ZHOAS ZE where
  type ZOk ZE a = ()
  zlift x = ZE x
  lam f   = ZE $ \a -> evalZE $ f (zlift a)
  app f a = ZE $ (evalZE f) (evalZE a)


--
-- The type ZDExpr interprets a ZHOAS as an expression that has both a value and
-- a derivative.
--

data ZDExpr a  = ZDE { zdeval :: a,
                       zdedelta:: PatchDelta a }


evalZDE :: (Patchable a) => ZDExpr a -> a
evalZDE = zdeval

instance ZHOAS ZDExpr where
  type ZOk ZDExpr a = Patchable a
  zlift a = ZDE a mempty
  lam zf = ZDE (\a -> zdeval (zf (zlift a)))
               (\a -> \da -> let aa = ZDE a da
                                 bb = zf aa
                             in zdedelta bb)
  app (ZDE f f') (ZDE a a') = ZDE (f a) ((f' a) a')



--
-- An alternate version of ZDExpr. 
-- The normal @ZDExpr@ has two fields @a@ and @da@
-- For example a function would look like
-- @ZDE (a -> b) (a -> da -> db)@
--
-- Note that both fields start with (a ->) so we can merge these into
-- a single function (a -> (b, da -> db))
--
-- The ZXFunc represents functions in this compacted form. Since both
-- @b@ and @da -> db@ are computed from @a@ there should be some work-sharing
-- happening in the code. The code for `app` is a lot messier in this version
-- though. It looks better when you use the CCC representation.
--

newtype DFunc a b = DF { unDF :: a -> b }

type instance PatchDelta (DFunc a b) = DFunc a ((PatchDelta a) -> (PatchDelta b))

data ZXExpr a where
  ZXFunc :: (DFunc a (b, PatchDelta a -> PatchDelta b)) -> ZXExpr (a -> b)
  ZXVal :: a -> PatchDelta a -> ZXExpr a

zxposition :: (Patchable a) => ZXExpr a -> a
zxposition (ZXVal a da) = a
zxposition (ZXFunc df) = fst . unDF df

zxvelocity :: (Patchable a) => ZXExpr a -> PatchDelta a
zxvelocity (ZXVal a da) = da
zxvelocity (ZXFunc df) = snd . unDF df

instance ZHOAS ZXExpr where
  type ZOk ZXExpr a = Patchable a
  zlift a = ZXVal a mempty
  -- DFunc here is a -> (b, da -> db)
  lam zf  = ZXFunc $ DF $ \a ->   let b = zxposition (zf (zlift a))
                                      dab = \da -> let aa = ZXVal a da
                                                       bb = zf aa
                                                   in zxvelocity bb
                                  in (b, dab)
  app (ZXFunc zf) za = let a = zxposition za
                           a' = zxvelocity za
                           (fa,fa') = (unDF zf) a
                           dfa = fa' a'
                       in ZXVal fa dfa
  app zf za = let f = zxposition zf
                  f' = zxvelocity zf
                  a = zxposition za
                  a' = zxvelocity za
                  fa = (f a)
                  dfa = ((f' a) a')
              in ZXVal fa dfa
                                                                  
