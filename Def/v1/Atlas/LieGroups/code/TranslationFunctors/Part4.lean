/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TranslationFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.FGUeaIotaRange
import Lemma.Int.All_Eq_0.of.EqCompositionLengthO_0.IsCategoryO
import Lemma.Int.IsCategoryOA.of.IsCategoryOB
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Def.v1.Atlas.LieGroups.code.BGGReciprocity.Part3
import Structure.v1.Atlas.LieGroups.code.TensorO
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Semisimple.Basic
import Structure.v1.Atlas.LieGroups.code.TranslationFunctors.Part2


noncomputable section

open scoped TensorProduct

universe uM

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable (Δ : TriangularDecomposition R 𝔤)

variable (rd : PositiveRootData Δ)

variable (wg : WeylGroupData Δ)

local notation "𝔥*" => (Δ.𝔥 →ₗ[R] R)

attribute [instance] TranslationFunctorData.V_addCommGroup
  TranslationFunctorData.V_module TranslationFunctorData.V_lieRingModule
  TranslationFunctorData.V_lieModule TranslationFunctorData.V_finiteDim
  TranslationFunctorData.V_irreducible

attribute [instance] TranslationFunctorData.ApplyResult.instAddCommGroup
  TranslationFunctorData.ApplyResult.instModule
  TranslationFunctorData.ApplyResult.instLieRingModule
  TranslationFunctorData.ApplyResult.instLieModule

def IsContragredientLieModule.symm
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module R W] [LieRingModule 𝔤 W] [LieModule R 𝔤 W]
    (h : IsContragredientLieModule (R := R) (𝔤 := 𝔤) V W) :
    IsContragredientLieModule (R := R) (𝔤 := 𝔤) W V where
  pairing :=
    { toFun := fun w =>
        { toFun := fun v => h.pairing v w
          map_add' := fun v₁ v₂ => by simp [map_add]
          map_smul' := fun r v => by simp [map_smul] }
      map_add' := fun w₁ w₂ => by
        ext v; simp [map_add]
      map_smul' := fun r w => by
        ext v; simp [map_smul] }
  nondegenerate_left := fun w hw => h.nondegenerate_right w (fun v => hw v)
  nondegenerate_right := fun v hv => h.nondegenerate_left v (fun w => hv w)
  equivariant := fun x w v => by
    have h_eq := h.equivariant x v w


    rw [add_comm]
    exact h_eq

def TwoSidedIdeal.toSubmoduleR {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (J : TwoSidedIdeal A) : Submodule R A where
  carrier := (J : Set A)
  add_mem' ha hb := J.add_mem ha hb
  zero_mem' := J.zero_mem
  smul_mem' r a ha := by rw [Algebra.smul_def]; exact J.mul_mem_left _ _ ha

noncomputable def idealToSubmoduleEvalAtV {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M] (act : A →ₐ[R] Module.End R M) (v : M) : A →ₗ[R] M where
  toFun u := act u v
  map_add' x y := by simp [map_add, LinearMap.add_apply]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    show act (r • x) v = r • (act x v)
    rw [Algebra.smul_def, map_mul]
    simp [AlgHom.commutes]

end
