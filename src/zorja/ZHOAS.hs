{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.ZHOAS where

import Data.Kind

import Zorja.Patchable


-- |'ZHOAS' is used for expressing your function as
-- a DSL, using HOAS (Higher-Order Abstrac Syntax).
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
class ZHOAS rep where
    type ZOk rep a :: Constraint
    lam :: (ZOk rep a, ZOk rep b, ZOk rep (a -> b)) => (rep a -> rep b) -> rep (a -> b)
    app :: (ZOk rep a, ZOk rep b, ZOk rep (a -> b)) => rep (a -> b) -> rep a -> rep b
    eval :: (ZOk rep a) => rep a -> a


-- |The type ZE lets you eval a ZHOAS expression as a simple value or function a -> b
newtype ZE a = ZE { unZE :: a }

instance ZHOAS ZE where
    type ZOk ZE a = ()
    lam f   = ZE $ \a -> eval $ f (ZE a)
    app f a = ZE $ (eval f) (eval a)
    eval (ZE a) = a


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
    ZDV :: (Patchable a) => a -> ILCDelta a -> ZDExpr a

zdValue :: (Patchable a) => ZDExpr a -> a
zdValue zv = fst $ zdEval zv

zdPatch :: (Patchable a) => ZDExpr a -> ILCDelta a
zdPatch zv = snd $ zdEval zv

zdApplyPatch :: (Patchable a) => ZDExpr a -> a
zdApplyPatch zv = let (x,dx) = zdEval zv
                  in patch x dx


zdEval :: (Patchable a) => ZDExpr a -> (a, ILCDelta a)
zdEval (ZDV a da) = (a, da)

instance ZHOAS ZDExpr where
    type ZOk ZDExpr a = Patchable a
    lam zf = ZDV (\a -> zdValue (zf (ZDV a noPatch)))
                 (\a da -> zdPatch (zf (ZDV a da)))
    app (ZDV f df) val = let (a,da) = zdEval val
                         in  ZDV (f a) (df a da)
    eval = zdApplyPatch
    
instance (Patchable a, Show a, Show (ILCDelta a)) => Show (ZDExpr a) where
    show (ZDV a da) = "(ZDExpr Value: " ++ show a ++ "," ++ show da ++ ")"


{-
data FunctorDeltaExpr a da = FDE a da (Iso' da a) deriving (Eq, Show)

instance (Functor f) => Functor (FunctorDeltaExpr f) where
    fmap f (FDE a fa) = FDE (f a) (fmap f fa)

instance (Applicative f) => Applicative (FunctorDeltaExpr f) where
    pure x = FDE x (pure x)
    (FDE f df) <*> (FDE a da) = FDE (f a) (df <*> da)


instance (Foldable f) => Foldable (FunctorDeltaExpr f) where
    foldMap f (FDE a fa) = (f a) <> (foldMap f fa)

instance (Traversable f) => Traversable (FunctorDeltaExpr f) where
    traverse f (FDE a fa) = FDE <$> (f a) <*> (traverse f fa)

instance (Distributive f) => Distributive (FunctorDeltaExpr f) where
    distribute fga = FDE (fmap gval fga) (collect gchange fga)
        where
            gval (FDE a _) = a
            gchange (FDE _ fa) = fa

instance (Functor f) => Comonad (FunctorDeltaExpr f) where
    extract (FDE a fa) = a
    duplicate x@(FDE a fa) = FDE x (fmap (const x) fa)
    extend f x@(FDE a fa) = FDE (f x) (fmap (const (f x)) fa)
-}

--
-- | A property of some data structures is that they
-- can represent adding or removing an element as a ZDExpr,
-- so they can be embedded into a structural changing data structure.
-- This allows us to use @Functor@ and @Foldable@ with data structures
-- that add and remove elements.
--
{-
data SDExpr a where
    SDF :: (SDExpr a -> SDExpr b) -> SDExpr (a -> b)
    SDV :: a -> ILCDelta a -> SDExpr a
    SDAdd :: a -> SDExpr a
    SDDelete :: a -> SDExpr a

class (Patchable a) => StructurePatchable a where
    fromSDExpr :: SDExpr a -> ZDExpr a
    toSDExpr :: ZDExpr a -> SDExpr a

instance ZHOAS SDExpr where
    type ZOk SDExpr a = StructurePatchable a
    lam sf = SDF sf
    app (SDF sf) x = sf x
    app (SDV f df) x = let (a,da) = zdEval $ fromSDExpr x
                       in  SDV (f a) (df a da)
    app (SDAdd f) x = undefined {-let (a,_) = zdEval $ fromSDExpr x
                      in SDAdd (f a)-}
    app (SDDelete f) x = undefined {-let (a,_) = zdEval $ fromSDExpr x
                         in SDDelete (f a)-}
-}

{-
-- | Functions as SDExprs
instance (Patchable (a -> b), StructurePatchable a, StructurePatchable b) => StructurePatchable (a -> b) where
    fromSDExpr (SDF sf)     = ZDF (fromSDExpr . sf . toSDExpr)
    fromSDExpr (SDV a da)   = ZDV a da
    -- figure out what these mean more rigorously before implementing them!
    fromSDExpr (SDAdd f)    = undefined {-ZDF $ \zx -> let (x,dx) = zdEval zx
                                           in fromSDExpr (SDAdd (f x))-}
    fromSDExpr (SDDelete f) = undefined {-ZDF $ \zx -> let (x,dx) = zdEval zx
                                           in fromSDExpr (SDDelete (f x))-}

    toSDExpr (ZDF zf) = SDF (toSDExpr . zf . fromSDExpr)
    toSDExpr (ZDV a da) = SDV a da
-}

--
-- Distributive typeclass over ZDExpr. Needed for catamorphism and friends
--



zdCompose :: (Patchable a, Patchable b, Patchable c) =>
  ZDExpr (b -> c) -> ZDExpr (a -> b) -> ZDExpr (a -> c)
zdCompose zbc zab = lam $ (app zbc) . (app zab)

zLiftFunction :: (Patchable a, Patchable b) => (a -> b) -> ZDExpr (a -> b)
zLiftFunction f = ZDV f df
    where
        df = \a -> \da -> let b = f a
                              b' = f (patch a da)
                          in
                              changes b b'


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

instance PatchInstance BoolChange where
    a <^< b = a <> b
    noPatch = mempty


newtype ZBool = ZBool { unZBool :: Bool } deriving (Eq)

type instance (ILCDelta ZBool) = BoolChange

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
                                        ZDV x1 (dx1 <^< patchedchanges)
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

type instance ILCDelta (DFunc a b) = DFunc a ((ILCDelta a) -> (ILCDelta b))

data ZXExpr a where
    ZXFunc :: (DFunc a (b, ILCDelta a -> ILCDelta b)) -> ZXExpr (a -> b)
    ZXVal :: a -> ILCDelta a -> ZXExpr a

zxposition :: ZXExpr a -> a
zxposition (ZXVal a _da) = a
zxposition (ZXFunc df) = fst . unDF df

zxvelocity :: ZXExpr a -> ILCDelta a
zxvelocity (ZXVal _a da) = da
zxvelocity (ZXFunc df) = snd . unDF df

instance ZHOAS ZXExpr where
    type ZOk ZXExpr a = Patchable a
    -- DFunc here is a -> (b, da -> db)
    lam zf  = ZXFunc $ DF $ \a -> let b = zxposition (zf (ZXVal a noPatch))
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
