{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Zorja.SumTypeWrapper where

import Language.Haskell.TH

-- mostly for bimapping on tuples returned by unbundleVD
import Data.Bifunctor

import Zorja.Patchable

import qualified GHC.Generics as GHC
import Generics.SOP

newtype SumTypeWrapper a = SumTypeWrapper a
  deriving (Eq, Show, GHC.Generic)

data SumTypeDelta a =
    SwitchTagDelta a
  | PatchTagDelta (ILCDelta a)
  deriving (GHC.Generic)

data SumTypeValDelta a =
    OneTag (ValDelta a)
  | ChangeTag a a
  deriving (GHC.Generic)

instance (Show a, Show (ILCDelta a)) => Show (SumTypeDelta a) where
  show (SwitchTagDelta da) = "SwitchTagDelta " ++ show da
  show (PatchTagDelta da) = "PatchTagDelta " ++ show da

instance (Show a, Show (ValDelta a)) => Show (SumTypeValDelta a) where
  show (OneTag aa) = "OneTag " ++ show aa
  show (ChangeTag a a') = "ChangeTag (" ++ show a ++ ") (" ++ show a' ++ ")"

type instance ILCDelta (SumTypeWrapper a) = SumTypeDelta a
type instance ValDelta (SumTypeWrapper a) = SumTypeValDelta a

instance DeltaRelation     (SumTypeWrapper a) (SumTypeDelta a)
instance FlipDeltaRelation (SumTypeDelta a)   (SumTypeWrapper a)
instance ValDeltaRelation     (SumTypeWrapper a)  (SumTypeValDelta a)
instance FlipValDeltaRelation (SumTypeValDelta a)  (SumTypeWrapper a)

instance (ValDeltaBundle a) => ValDeltaBundle (SumTypeWrapper a) where
  bundleVD (SumTypeWrapper a,SwitchTagDelta a') = ChangeTag a a'
  bundleVD (SumTypeWrapper a,PatchTagDelta da) = OneTag (bundleVD (a,da))

  unbundleVD (OneTag aa)      = bimap SumTypeWrapper PatchTagDelta $ unbundleVD aa
  unbundleVD (ChangeTag a a') = (SumTypeWrapper a, SwitchTagDelta a')                           

  valueBundle (SumTypeWrapper a) = OneTag (valueBundle a)

instance (Patchable a, Generic a) => Patchable (SumTypeWrapper a) where
  patch (OneTag aa) = SumTypeWrapper (patch aa)
  patch (ChangeTag _ a') = SumTypeWrapper a'

  diffBundle (SumTypeWrapper a) (SumTypeWrapper a')
    | sameConstructors a a' = OneTag (diffBundle a a')
    | otherwise             = ChangeTag a a'

  changes (SumTypeWrapper a) (SumTypeWrapper a')
    | sameConstructors a a' = PatchTagDelta (changes a a')
    | otherwise             = SwitchTagDelta a'

instance (Patchable a) => PatchInstance (SumTypeDelta a) where
  _                  <^< SwitchTagDelta da'  = SwitchTagDelta da'
  (SwitchTagDelta a) <^< (PatchTagDelta da') = SwitchTagDelta (patch (bundleVD (a,da')))
  (PatchTagDelta da) <^< (PatchTagDelta da') = PatchTagDelta (da <^< da')


-- Returns true if the two values use the same constructor from a given sum type.
-- SOP types represent the different constructos using a Peano encoding
-- of the constructor number, so (Z ...) is the first constructor, (S (Z ...))
-- is the second constructor, and so on. Here we just compare constructors, and
-- if the S/Z counts match the constructors are the same. If the S/Z counts
-- don't match these are two different constructors.
sameConstructors :: (Generic a) => a -> a -> Bool
sameConstructors a b = cs (from a) (from b)
  where
    cs :: SOP I xss -> SOP I xss -> Bool
    cs (SOP (Z _))   (SOP (Z _))   = True
    cs (SOP (S xss)) (SOP (S yss)) = cs (SOP xss) (SOP yss)
    cs _             _             = False



--
-- Take a case statement/pattern match for a sum type and convert into a ValDelta - based function
--
dCase :: (Patchable a, Patchable b) => ((SumTypeWrapper a) -> b) -> (SumTypeValDelta a) -> ValDelta b
dCase fc (OneTag aa) = let a = valueUnbundle aa
                           b = fc (SumTypeWrapper a)
                           b' = fc (SumTypeWrapper (patch aa))
                       in
                          diffBundle b b'
dCase fc (ChangeTag a a') =
  let b = fc (SumTypeWrapper a)
      b' = fc (SumTypeWrapper a')
  in diffBundle b b'





--------------------------------------------
--
-- Template haskell to auto-generate ILCDelta and ValDelta for data types via Generics
--
-------------------------------------------

data DeltaizeConfig = DeltaizeConfig
  {
    suffix :: String,
    deltaTFName :: Name
  }

--
-- given the name of a type A generates type instances for delta/valdelta:
--
genTypeInstances :: Name -> Q [Dec]
genTypeInstances n =
  do
    let base = nameBase n
    inf <- reify n
    let typeVarsXXXX = getTypeVars inf
    let typeVars = [mkName "argh"]
    Just ndelta <- lookupTypeName (base ++ "_delta")
    Just nvaldelta <- lookupTypeName (base ++ "_valdelta")
    Just deltaTF <- lookupTypeName "ILCDelta"
    Just valdeltaTF <- lookupTypeName "ValDelta"

    let nType = genType n typeVars
    let nDeltaType = genType ndelta typeVars
    let nValDeltaType = genType nvaldelta typeVars
    -- 
    return [
      -- "type instance (ILCDelta A) = A_delta"
      (TySynInstD $ TySynEqn Nothing (AppT (ConT deltaTF) nType) nDeltaType),
      -- "type instance (ValDelta A) = A_valdelta"
      (TySynInstD $ TySynEqn Nothing (AppT (ConT valdeltaTF) nType) nValDeltaType)
      ]

-- | Given a name generates the typeclass instances for SOP style Generics and Generic-generated
--   instances for:
--    - Patchable
--    - PatchInstance
--    - ValDeltaBundle
--
-- If Generics won't work for your datatype then you will have to generate these yourself.
--

getTypeVars :: Info -> [Name]
getTypeVars (TyConI (DataD _ctxt _name tvb _mk _cons _deriv)) = fmap getBindName tvb
  where
    getBindName (PlainTV n) = n
    getBindName (KindedTV n _k) = n
getTypeVars _ = []

genType :: Name -> [Name] -> Type
genType n [] = ConT n
genType n (x:xs) = AppT (genType n xs) (VarT x)

genContext :: Name -> [Name] -> [Pred]
genContext req xs = fmap (appC req) xs
  where
    appC c v = (AppT (ConT c) (VarT v))

genPatchablePrerequisites :: [Name] -> Q [Pred]
genPatchablePrerequisites xs =
  do
    Just patchableClass <- lookupTypeName "Patchable"
    let patchC v = (AppT (ConT patchableClass) (VarT v))
    drs <- genDeltaRelations xs
    vdrs <- genValDeltaRelations xs
    return $ (fmap patchC xs) ++ drs ++ vdrs

genPatchInstancePrerequisites :: [Name] -> Q [Pred]
genPatchInstancePrerequisites xs =
  do
    Just patchInstanceClass <- lookupTypeName "PatchInstance"
    Just deltaFamily <- lookupTypeName "ILCDelta"
    let patchIC v = (AppT (ConT patchInstanceClass) (AppT (ConT deltaFamily) (VarT v)))
    return (fmap patchIC xs)

genValDeltaBundlePrerequisites :: [Name] -> Q [Pred]
genValDeltaBundlePrerequisites xs =
  do
    Just valDeltaBundleClass <- lookupTypeName "ValDeltaBundle"
    let valDeltaBundleC v = (AppT (ConT valDeltaBundleClass) (VarT v))
    drs <- genDeltaRelations xs
    vdrs <- genValDeltaRelations xs
    return $ (fmap valDeltaBundleC xs) ++ drs ++ vdrs


genDeltaRelations :: [Name] -> Q [Pred]
genDeltaRelations xs =
  do
    Just deltaFamily <- lookupTypeName "ILCDelta"
    Just deltaRelationClass <- lookupTypeName "DeltaRelation"
    Just flipDeltaRelationClass <- lookupTypeName "FlipDeltaRelation"
    let nType v = (VarT v)
    let nDeltaType v = (AppT (ConT deltaFamily) (VarT v))
    let dC    v = (AppT (AppT (ConT     deltaRelationClass)      (nType v)) (nDeltaType v))
    let fdC   v = (AppT (AppT (ConT flipDeltaRelationClass) (nDeltaType v))      (nType v))
    return $ (fmap dC xs) ++ (fmap fdC xs)

genValDeltaRelations :: [Name] -> Q [Pred]
genValDeltaRelations xs =
  do
    Just valDeltaFamily <- lookupTypeName "ValDelta"
    Just valDeltaRelationClass <- lookupTypeName "ValDeltaRelation"
    Just flipValDeltaRelationClass <- lookupTypeName "FlipValDeltaRelation"
    let vdC    v = (AppT (AppT (ConT     valDeltaRelationClass)                              (VarT v)) (AppT (ConT valDeltaFamily) (VarT v)))
    let fvdC   v = (AppT (AppT (ConT flipValDeltaRelationClass) (AppT (ConT valDeltaFamily) (VarT v)))                              (VarT v))
    return $ (fmap vdC xs) ++ (fmap fvdC xs)


genClassInstances :: Name -> Q [Dec]
genClassInstances n =
  do
    inf <- reify n
    let typeVars = getTypeVars inf
    let base = nameBase n
    Just ndelta <- lookupTypeName (base ++ "_delta")
    Just nvaldelta <- lookupTypeName (base ++ "_valdelta")
    Just genericName <- lookupTypeName "Generic"
    Just valdeltaClass <- lookupTypeName "ValDeltaBundle"
    Just patchinstanceClass <- lookupTypeName "PatchInstance"
    Just patchableClass <- lookupTypeName "Patchable"
    Just deltaRelationClass <- lookupTypeName "DeltaRelation"
    Just flipDeltaRelationClass <- lookupTypeName "FlipDeltaRelation"
    Just valDeltaRelationClass <- lookupTypeName "ValDeltaRelation"
    Just flipValDeltaRelationClass <- lookupTypeName "FlipValDeltaRelation"

    patchablePrerequisites <- genPatchablePrerequisites typeVars
    patchInstancePrerequisites <- genPatchInstancePrerequisites typeVars
    valDeltaBundlePrerequisites <- genValDeltaBundlePrerequisites typeVars

    let nType = genType n typeVars
    let nDeltaType = genType ndelta typeVars
    let nValDeltaType = genType nvaldelta typeVars
    return [
        -- "instance Generic A"
        (InstanceD Nothing [] (AppT (ConT genericName) nType) []),
        -- "instance Generic A_delta"
        (InstanceD Nothing [] (AppT (ConT genericName) nDeltaType) []),
        -- "instance Generic A_valdelta"
        (InstanceD Nothing [] (AppT (ConT genericName) nValDeltaType) []),
        -- "instance ValDeltaBundle A"
        (InstanceD Nothing valDeltaBundlePrerequisites (AppT (ConT valdeltaClass) nType) []),
        -- "instance PatchInstance A_delta"
        (InstanceD Nothing patchInstancePrerequisites (AppT (ConT patchinstanceClass) nDeltaType) []),
        -- "instance (Patchable a,..) => Patchable A"
        (InstanceD Nothing patchablePrerequisites (AppT (ConT patchableClass) nType) []),
        -- "instance DeltaRelation A A_delta"
        (InstanceD Nothing [] (AppT (AppT (ConT deltaRelationClass) nType) nDeltaType) []),
        -- "instance FlipDeltaRelation A_delta A"
        (InstanceD Nothing [] (AppT (AppT (ConT flipDeltaRelationClass) nDeltaType) nType) []),
        -- "instance ValDeltaRelation A A_valdelta"
        (InstanceD Nothing [] (AppT (AppT (ConT valDeltaRelationClass) nType) nValDeltaType) []),
        -- "instance FlipValDeltaRelation A_valdelta A"
        (InstanceD Nothing [] (AppT (AppT (ConT flipValDeltaRelationClass) nValDeltaType) nType) [])
      ]

--
-- given the name of a sum type A generate the delta and valdelta of A,
-- naming them A_delta and A_valdelta
--
genDeltaDataTypes :: Name -> Q [Dec]
genDeltaDataTypes n =
  do
    inf <- reify n
    -- Generate two DeltaizeConfigs, one for ILCDelta and one for ValDelta.
    -- We also generate names.
    Just deltaTF <- lookupTypeName "ILCDelta"
    let deltaconfig    = (DeltaizeConfig "_delta" deltaTF)
    Just valdeltaTF <- lookupTypeName "ValDelta"
    let valdeltaconfig = (DeltaizeConfig "_valdelta" valdeltaTF)
    case inf of
      (TyConI dec)       -> sequenceA
                              [ 
                                -- data A_delta ...
                                (deltaDec deltaconfig dec), 
                                -- data A_valdelta ...
                                (deltaDec valdeltaconfig dec)
                              ]
      _                  -> return [  ]


-- | Convert a data declaration to it's equivalent ILCDelta or ValDelta,
--   depending on the DeltaizeConfig passed in. Also renames the data type and
--   constructors.
deltaDec :: DeltaizeConfig -> Dec -> Q Dec
deltaDec dconfig (DataD ctxt name tvb mk cons deriv) =
  do 
    -- modify constructors
    cons' <- traverse (deltaizeC dconfig) cons
    -- rename from 'A' to 'A_delta' or 'A_valdelta'  the suffix to use
    -- is specified in the DeltaizeConfig
    let name' = mkName ((nameBase name) ++ (suffix dconfig))
    Just genericName <- lookupTypeName "GHC.Generic"
    -- original is A
    -- this builds A_<suffix>
    let derivingGenericClause = [DerivClause Nothing [ConT genericName]]
    -- "data <name'> = (..constructors...)"
    return (DataD ctxt name' tvb mk cons' derivingGenericClause)
deltaDec _ _ =
    let k = mkName "Unknown"
    in return $ DataD [] k [] Nothing [] [] 

-- | Given a specific constructor this renames the constructor and converts
--   the type. As an example if the original constructor was 'Tag1 A' this
--   would rename it 'Tag1_delta (ILCDelta a)' or 'Tag1_valdelta (ValDelta a)'
--   depending on the DeltaizeConfig that was passed in. If the constructor
--   is not a normal constructor it is passed through unchanged.
deltaizeC :: DeltaizeConfig -> Con -> Q Con
deltaizeC dconfig (NormalC name bts) =
  do
    let finalName = mkName ((nameBase name) ++ (suffix dconfig))
    bts' <- traverse (deltaBT dconfig) bts
    return $ NormalC finalName bts'
deltaizeC _ c = return c

-- | Converts the type in a BangType to an ILC type.
--  If the original type is
--  'A' this changes it to 'ILCDelta A' or 'ValDelta A' depending on
--  the 'DeltaizeConfig' passed in.
deltaBT :: DeltaizeConfig -> (Bang,Type) -> Q (Bang,Type)
deltaBT dconfig (b,t) =
  do
    let vn = (deltaTFName dconfig)
    return (b,AppT (ConT vn) t)

