{-# LANGUAGE TemplateHaskell #-}

module Zorja.PatchableTH 
  (genDeltaDataTypes,
   genDeltaInstances)
  where

import Language.Haskell.TH


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
-- | Given the name of a sum type A generate the delta and valdelta of A,
-- naming them A_delta and A_valdelta
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
    maybeGenericName <- lookupTypeName "GHC.Generic"
    case maybeGenericName of
      Nothing -> fail "cannot find GHC.Generic, import as: 'import qualified GHC.Generics as GHC'"
      Just genericName ->
        do
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


-- | Generate ILC type instances and typeclasses for the name data type.
--   You'll need to have already generated the delta datatypes either by hand or using 'genDeltaDataTypes'
genDeltaInstances :: Name -> Q [Dec]
genDeltaInstances n =
  do
    ti <- genTypeInstances n
    ci <- genClassInstances n
    return $ ti ++ ci

--
-- given the name of a type A generates type instances for delta/valdelta:
--
genTypeInstances :: Name -> Q [Dec]
genTypeInstances n =
  do
    let base = nameBase n
    inf <- reify n
    let typeVars = getTypeVars inf
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

