{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

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


--
-- The type ZE lets you eval a ZHOAS expression as a simple value or function a -> b
--

newtype ZE a = ZE { unZE :: a }

evalZE :: ZE a -> a
evalZE = unZE

instance ZHOAS ZE where
    type ZOk ZE a = ()
    lam f   = ZE $ \a -> evalZE $ f (ZE a)
    app f a = ZE $ (evalZE f) (evalZE a)


--
-- The type ZDExpr interprets a ZHOAS as an expression that has both a value and
-- a derivative.
-- If you just wanted values you could in fact just use a ZDExpr instead of a
-- ZE and pull out only the values. Because of laziness the deltas would never
-- get evaluated so you wouldn't pay for evaluating the deltas. However, ZE
-- is still better if you don't need deltas. Since ZE is a newtype it doesn't
-- incur any runtime overhead.
--

-- For Functions @f@ the delta @df@ contains both the derivative @f'@ and
-- the function delta @Del f@ which holds deltas due to applied arguments.
-- This all gets wrapped up into (ZDExpr a -> ZDExpr b) so it's not
-- obvious here.

data ZDExpr a where
    ZDF :: (Patchable a, Patchable b) => (ZDExpr a -> ZDExpr b) -> ZDExpr (a -> b)
    ZDV :: (Patchable a) => a -> PatchDelta a -> ZDExpr a

zdEval :: (Patchable a) => ZDExpr a -> (a, PatchDelta a)
zdEval (ZDF zf)   = let f  = \a ->        zdValue $ zf (ZDV a mempty)
                        df = \a -> \da -> zdPatch $ zf (ZDV a da)
                    in
                        (f, df)
zdEval (ZDV a da) = (a, da)

instance (Patchable a, Show a, Show (PatchDelta a)) => Show (ZDExpr a) where
    show (ZDF zf) = "(ZDExpr Function)"
    show (ZDV a da) = "(ZDExpr Value: " ++ show a ++ "," ++ show da ++ ")"

--
-- Functor type for ZDExprs. For this to work both a and da must be
-- functors.
--
class ZDFunctor (zf :: * -> *) where
    zdmap :: ZDExpr (a -> b) -> ZDExpr (zf a) -> ZDExpr (zf b)

class ZDStructFunctor (zf :: * -> *) where
    zdstructuremap :: (StructurePatchable a, StructurePatchable b) =>
             ZDExpr (a -> b) -> ZDExpr (zf a) -> ZDExpr (zf b)

--
-- Distributive typeclass over ZDExpr. Needed for catamorphism and friends
--
class ZDDistributive (zf :: * -> *) where
    zddist :: (StructurePatchable a) => ZDExpr (zf a) -> zf (ZDExpr a)

zdValue :: (Patchable a) => ZDExpr a -> a
zdValue zv = fst $ zdEval zv

zdPatch :: (Patchable a) => ZDExpr a -> PatchDelta a
zdPatch zv = snd $ zdEval zv

zdCompose :: (Patchable a, Patchable b, Patchable c) =>
  ZDExpr (b -> c) -> ZDExpr (a -> b) -> ZDExpr (a -> c)
zdCompose zbc zab = lam $ (app zbc) . (app zab)

instance ZHOAS ZDExpr where
    type ZOk ZDExpr a = Patchable a
    lam zf = ZDF zf
    app (ZDF zf) a = zf a
    app (ZDV f df) val = let (a,da) = zdEval val
                         in
                             ZDV (f a) (df a da)

zLiftFunction :: (Patchable a, Patchable b) => (a -> b) -> ZDExpr (a -> b)
zLiftFunction f = ZDV f df
    where
        df = \a -> \da -> let b = f a
                              b' = f (patch a da)
                          in
                              changes b b'


--
-- A property of some data structures is that they
-- can represent adding or removing an element as a ZDExpr,
-- so they can be embedded into a structural changing data structure.
--
data SDExpr a =
      SDJust (ZDExpr a)
    | SDAdd a
    | SDDelete a

class (Patchable a) => StructurePatchable a where
    fromSDExpr :: SDExpr a -> ZDExpr a
    toSDExpr :: ZDExpr a -> SDExpr a
 
--
-- Bool and if for ZDExpr
--

data BoolChange = NotVal | NoChange

instance Semigroup (BoolChange) where
    NotVal <> NotVal = NoChange
    a <> NoChange = a
    NoChange <> a = a

instance Monoid (BoolChange) where
    mempty = NoChange
    mappend = (<>)


newtype ZBool = ZBool { unZBool :: Bool } deriving (Eq)

type instance (PatchDelta ZBool) = BoolChange

instance Patchable ZBool where
    patch a da = case da of
                     NotVal   -> (ZBool . not . unZBool) a
                     NoChange -> a
    changes a b = if a == b
                  then NoChange
                  else NotVal


instance Semigroup ZBool where
    (ZBool a) <> (ZBool b) = ZBool (a || b)


zIf :: (Patchable a, Patchable b) => ZDExpr (a -> ZBool) -> ZDExpr b -> ZDExpr b -> ZDExpr (a -> b)
zIf = 
    \zpred -> 
        \zthen -> 
            \zelse ->
                lam $ \za ->
                    case (zdEval (zpred `app` za)) of
                        -- if the predicate doesn't change after the delta
                        -- is applied, we don't have to diff anything
                        (zb, NoChange) -> if (unZBool zb) then zthen else zelse
                        -- if the predicate result switches values after
                        -- patching, we have to diff between
                        -- the then and else clauses
                        (zb, NotVal) ->
                            let switchbool = \z1 z2 -> 
                                    let (x1,dx1) = zdEval z1
                                        (x2,dx2) = zdEval z2
                                        patchedchanges = changes (patch x1 dx1) (patch x2 dx2)
                                    in
                                        ZDV x1 (dx1 <> patchedchanges)
                            in
                                if (unZBool zb)
                                then -- true to false
                                    switchbool zthen zelse
                                else -- false to true
                                    switchbool zelse zthen

--      
-- An experimental version of ZDExpr. 
-- The normal @ZDExpr@ has two fields @a@ and @da@
-- For example a function would look like
-- @ZDE (a -> b) (a -> da -> db)@
--
-- Noting that both fields start with (a ->) we can merge these two
-- functions (a -> b) and (a -> da -> db) into
-- a single function (a -> (b, da -> db))
--
-- The ZXFunc represents functions in this compacted form. Since both
-- @b@ and @da -> db@ are computed from @a@ there should be some work-sharing
-- happening in the code. The code for `app` is a lot messier in this version
-- though. The code for this looks better when you use the CCC representation,
-- which is in ZCCC.hs
--

newtype DFunc a b = DF { unDF :: a -> b }

type instance PatchDelta (DFunc a b) = DFunc a ((PatchDelta a) -> (PatchDelta b))

data ZXExpr a where
    ZXFunc :: (DFunc a (b, PatchDelta a -> PatchDelta b)) -> ZXExpr (a -> b)
    ZXVal :: a -> PatchDelta a -> ZXExpr a

zxposition :: (Patchable a) => ZXExpr a -> a
zxposition (ZXVal a _da) = a
zxposition (ZXFunc df) = fst . unDF df

zxvelocity :: (Patchable a) => ZXExpr a -> PatchDelta a
zxvelocity (ZXVal _a da) = da
zxvelocity (ZXFunc df) = snd . unDF df

instance ZHOAS ZXExpr where
    type ZOk ZXExpr a = Patchable a
    -- DFunc here is a -> (b, da -> db)
    lam zf  = ZXFunc $ DF $ \a -> let b = zxposition (zf (ZXVal a mempty))
                                      dab = \da -> let aa = ZXVal a da
                                                       bb = zf aa
                                                   in zxvelocity bb
                                  in (b, dab)                                  
    --
    -- app on a ZXFunc can take a bit of a shortcut
    --
    -- note that we can't re-pack the result into a ZXFunc since we don't know
    -- if (f a) and ((f' a) a') are functions or not.
    --
    app (ZXFunc zf) za =  let a = zxposition za
                              a' = zxvelocity za
                              (fa,fa') = (unDF zf) a
                              -- fa  = (f a)
                              -- fa' = (f' a)
                          in ZXVal fa (fa' a')
    app zf za = let f = zxposition zf
                    f' = zxvelocity zf
                    a = zxposition za
                    a' = zxvelocity za
                in ZXVal (f a) ((f' a) a')
