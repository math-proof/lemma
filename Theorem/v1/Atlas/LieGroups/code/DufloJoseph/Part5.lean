/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Lemma.Fin.Any_Eq.of.Ne_0
import Lemma.Complex.Any_Any_And_All_Eq_AdjointAction.All_Finite.of.IsHarishChandraBimodule.IsIrreducible
import Def.v1.Atlas.LieGroups.code.HighestWeightModules.Part2
import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part5


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

theorem isFiniteTypeMap_comp_mk_tensor
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (v : V) (T : M →ₗ[R] N) (hT : IsFiniteTypeMap (𝔤 := 𝔤) M N T) :
    IsFiniteTypeMap (𝔤 := 𝔤) M (TensorProduct R V N)
      ((TensorProduct.mk R V N v).comp T) := by

  obtain ⟨S, hfin, hT_mem, hstab⟩ := hT

  let Φ : TensorProduct R V S →ₗ[R] (M →ₗ[R] TensorProduct R V N) :=
    TensorProduct.lift
      { toFun := fun w =>
          { toFun := fun g => (TensorProduct.mk R V N w).comp (g : M →ₗ[R] N)
            map_add' := fun g₁ g₂ => by ext m; simp [LinearMap.comp_apply, map_add]
            map_smul' := fun r g => by ext m; simp [LinearMap.comp_apply, map_smul] }
        map_add' := fun w₁ w₂ => by
          ext g : 1; ext m; simp [TensorProduct.mk]
        map_smul' := fun r w => by
          ext g : 1; ext m; simp [TensorProduct.mk, TensorProduct.smul_tmul'] }

  have hΦ_tmul : ∀ (w : V) (g : S), Φ (w ⊗ₜ[R] g) = (TensorProduct.mk R V N w).comp (g : M →ₗ[R] N) := by
    intro w g; simp [Φ, TensorProduct.lift.tmul]

  let S' : Submodule R (M →ₗ[R] TensorProduct R V N) := LinearMap.range Φ

  haveI : Module.Finite R (TensorProduct R V S) := Module.Finite.tensorProduct R V S
  haveI : Module.Finite R S' := Module.Finite.range Φ
  refine ⟨S', inferInstance, ?_, ?_⟩
  ·
    exact ⟨v ⊗ₜ[R] ⟨T, hT_mem⟩, hΦ_tmul v ⟨T, hT_mem⟩⟩
  ·
    intro x f hf

    obtain ⟨z, rfl⟩ := hf

    induction z using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      have : adjointActionOnHom (R := R) (𝔤 := 𝔤) M (TensorProduct R V N) x 0 = 0 := by
        ext m; simp [adjointActionOnHom]
      rw [this]; exact zero_mem _
    | tmul w g =>


      have key : adjointActionOnHom M (TensorProduct R V N) x
            ((TensorProduct.mk R V N w).comp (g : M →ₗ[R] N)) =
          (TensorProduct.mk R V N ⁅x, w⁆).comp (g : M →ₗ[R] N) +
          (TensorProduct.mk R V N w).comp (adjointActionOnHom M N x (g : M →ₗ[R] N)) := by
        ext m
        simp only [adjointActionOnHom, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
          TensorProduct.mk_apply, LinearMap.add_apply]
        rw [TensorProduct.LieModule.lie_tmul_right]
        rw [add_sub_assoc]
        congr 1
        rw [← TensorProduct.tmul_sub]
      rw [hΦ_tmul, key]
      have hg_stab : adjointActionOnHom M N x (g : M →ₗ[R] N) ∈ S :=
        hstab x g g.property
      exact ⟨⁅x, w⁆ ⊗ₜ[R] g + w ⊗ₜ[R] ⟨adjointActionOnHom M N x (g : M →ₗ[R] N), hg_stab⟩, by
        rw [map_add, hΦ_tmul, hΦ_tmul]⟩
    | add z₁ z₂ ih₁ ih₂ =>

      have hadj_add : adjointActionOnHom M (TensorProduct R V N) x (Φ (z₁ + z₂)) =
          adjointActionOnHom M (TensorProduct R V N) x (Φ z₁) +
          adjointActionOnHom M (TensorProduct R V N) x (Φ z₂) := by
        simp only [map_add]
        ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
      rw [hadj_add]
      exact Submodule.add_mem S' ih₁ ih₂

end
