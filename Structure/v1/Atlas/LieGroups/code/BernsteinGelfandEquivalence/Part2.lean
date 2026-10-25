/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BernsteinGelfandEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.HCBimoduleProjectives.Part2
import Lemma.Fin.All_Eq.of.All_Eq.All_Eq_RightAction.All_Eq_RightAction.All_Any_Eq_Sum_RightAction
import Lemma.Int.IsInQPlus0
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.Level1.ne.Top
import Lemma.Int.FGUeaIotaRange
import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Def.v1.Atlas.LieGroups.code.JantzenFiltration.Part2
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Basic
import Def.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence


noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

structure LieModuleMor
    (R : Type u_R) [CommRing R]
    (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (X Y : LieModuleObj.{u_R, u_g, u_mod} R g) where
  toLinearMap : X.carrier →ₗ[R] Y.carrier
  lie_compat : ∀ (x : g) (m : X.carrier),
    toLinearMap (⁅x, m⁆) = ⁅x, toLinearMap m⁆

structure LieModuleIso
    (R : Type u_R) [CommRing R]
    (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (X Y : LieModuleObj.{u_R, u_g, u_mod} R g) where
  forward : LieModuleMor R g X Y
  backward : LieModuleMor R g Y X
  left_inv : ∀ m : X.carrier,
    backward.toLinearMap (forward.toLinearMap m) = m
  right_inv : ∀ m : Y.carrier,
    forward.toLinearMap (backward.toLinearMap m) = m

structure TlambdaData
    (theta : CenterCharacter R g) where
  applyObj :
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) →
    (hY : IsInHCThetaOne Y theta) →
    LieModuleObj.{u_R, u_g, u_mod} R g
  applyHom :
    {Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂ →
    LieModuleMor R g (applyObj Y₁ hY₁) (applyObj Y₂ hY₂)
  applyHom_comp :
    {Y₁ Y₂ Y₃ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    {hY₃ : IsInHCThetaOne Y₃ theta} →
    (g' : HCThetaOneHom Y₂ Y₃ theta hY₂ hY₃) →
    (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    (comp_gf : HCThetaOneHom Y₁ Y₃ theta hY₁ hY₃) →
    comp_gf.toLinearMap = g'.toLinearMap.comp f.toLinearMap →
    (applyHom comp_gf).toLinearMap = (applyHom g').toLinearMap.comp (applyHom f).toLinearMap
  applyHom_id :
    {Y : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY : IsInHCThetaOne Y theta} →
    (idY : HCThetaOneHom Y Y theta hY hY) →
    idY.toLinearMap = LinearMap.id →
    (applyHom idY).toLinearMap = LinearMap.id
  applyHom_surjective :
    {Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    Function.Surjective f.toLinearMap →
    Function.Surjective (applyHom f).toLinearMap
  applyHom_exact :
    {Y₁ Y₂ Y₃ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    {hY₃ : IsInHCThetaOne Y₃ theta} →
    (p₁ : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    (p₀ : HCThetaOneHom Y₂ Y₃ theta hY₂ hY₃) →
    Function.Exact p₁.toLinearMap p₀.toLinearMap →
    Function.Surjective p₀.toLinearMap →
    Function.Exact (applyHom p₁).toLinearMap (applyHom p₀).toLinearMap
  applyObj_isCategoryO :
    {D : TriangularDecomposition R g} →
    {rd : PositiveRootData D} →
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) →
    (hY : IsInHCThetaOne Y theta) →
    IsCategoryO D rd (applyObj Y hY).carrier

structure HlambdaData
    (theta : CenterCharacter R g) where
  applyObj :
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) →
    LieBimodule.{u_R, u_g, u_mod} R g
  inHCThetaOne :
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) →
    IsInHCThetaOne (applyObj X) theta

structure IsInBlock_LambdaPlusP
    {D : TriangularDecomposition R g}
    (rd : PositiveRootData D)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g)
    (theta : CenterCharacter R g) : Prop where
  inCategoryO : IsCategoryO D rd X.carrier
  existsUEAAction :
    ∃ (ueaAct : UniversalEnvelopingAlgebra R g →ₐ[R] Module.End R X.carrier),
      GeneralizedEigenspaceCenter X.carrier ueaAct theta = ⊤

end
