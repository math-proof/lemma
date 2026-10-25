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
import Abbrev.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence


noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

def HCThetaOneHomBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (A B : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : Type u_mod :=
  HCThetaOneHom A.1 B.1 theta A.2 B.2

def TlambdaObjBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : LieModuleObj.{u_R, u_g, u_mod} R g :=
  Tl.applyObj A.1 A.2

def TlambdaMapBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {A B : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (f : HCThetaOneHomBundled theta A B) :
    LieModuleMor R g (TlambdaObjBundled Tl A) (TlambdaObjBundled Tl B) :=
  Tl.applyHom f

def IsProjHCBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : Prop :=
  IsProjectiveInHCThetaOne A.1 theta A.2

noncomputable def HCThetaOne_comp
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {A B C : HCThetaOneObj.{u_R, u_g, u_mod} R g theta} :
    HCThetaOneHomBundled theta B C → HCThetaOneHomBundled theta A B →
    HCThetaOneHomBundled theta A C :=
  fun g' f => {
    toLinearMap := g'.toLinearMap.comp f.toLinearMap
    left_compat := fun u m => by
      simp [LinearMap.comp_apply]
      rw [f.left_compat, g'.left_compat]
    right_compat := fun u m => by
      simp [LinearMap.comp_apply]
      rw [f.right_compat, g'.right_compat]
  }

def LieModuleMor_comp
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {X Y Z : LieModuleObj.{u_R, u_g, u_mod} R g}
    (g' : LieModuleMor R g Y Z) (f : LieModuleMor R g X Y) :
    LieModuleMor R g X Z where
  toLinearMap := g'.toLinearMap.comp f.toLinearMap
  lie_compat x m := by
    simp [LinearMap.comp_apply]
    rw [f.lie_compat, g'.lie_compat]

def LieModuleMor_sub
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f g' : LieModuleMor R g X Y) : LieModuleMor R g X Y where
  toLinearMap := f.toLinearMap - g'.toLinearMap
  lie_compat x m := by
    simp only [LinearMap.sub_apply]
    rw [f.lie_compat, g'.lie_compat, lie_sub]

noncomputable def HCThetaOne_id
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) :
    HCThetaOneHomBundled theta A A :=
  { toLinearMap := LinearMap.id
    left_compat := fun _ _ => rfl
    right_compat := fun _ _ => rfl }

def LieModuleMor_id
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) :
    LieModuleMor R g X X where
  toLinearMap := LinearMap.id
  lie_compat _ _ := rfl

def IsPresentationHC
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {P₁ P₀ X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀) (p₀ : HCThetaOneHomBundled theta P₀ X) : Prop :=
  Function.Surjective p₀.toLinearMap ∧
  (∀ m : P₁.1.carrier, p₀.toLinearMap (p₁.toLinearMap m) = 0) ∧
  (∀ m : P₀.1.carrier, p₀.toLinearMap m = 0 → ∃ n : P₁.1.carrier, p₁.toLinearMap n = m)

def IsPresentationO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Q₁ Q₀ Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g Q₁ Q₀) (q₀ : LieModuleMor R g Q₀ Y) : Prop :=
  Function.Surjective q₀.toLinearMap ∧
  (∀ m : Q₁.carrier, q₀.toLinearMap (q₁.toLinearMap m) = 0) ∧
  (∀ m : Q₀.carrier, q₀.toLinearMap m = 0 → ∃ n : Q₁.carrier, q₁.toLinearMap n = m)

def IsProjO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (P : LieModuleObj.{u_R, u_g, u_mod} R g) : Prop :=
  ∀ (Y₁ Y₂ : LieModuleObj.{u_R, u_g, u_mod} R g)
    (g' : LieModuleMor R g Y₁ Y₂) (f : LieModuleMor R g P Y₂),
    Function.Surjective g'.toLinearMap →
    ∃ (f' : LieModuleMor R g P Y₁),
      ∀ m : P.carrier, g'.toLinearMap (f'.toLinearMap m) = f.toLinearMap m

def IsIsoO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Y₁ Y₂ : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g Y₁ Y₂) : Prop :=
  ∃ (g' : LieModuleMor R g Y₂ Y₁),
    (∀ m : Y₁.carrier, g'.toLinearMap (f.toLinearMap m) = m) ∧
    (∀ m : Y₂.carrier, f.toLinearMap (g'.toLinearMap m) = m)

end
