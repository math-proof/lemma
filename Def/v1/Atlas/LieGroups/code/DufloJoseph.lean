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


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

def evalHC (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    (Δ.𝔥 →ₗ[R] R) →
    (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  fun wt =>
    (evalWeight Δ (wt + wg.ρ)).comp
      (wg.invariantSubalgebra.val.comp (chevalley_restriction_hc_iso Δ wg).toAlgHom)

def adjointActionOnHom
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : M →ₗ[R] N) : M →ₗ[R] N where
  toFun m := ⁅x, T m⁆ - T ⁅x, m⁆
  map_add' a b := by simp [lie_add, sub_add_sub_comm]
  map_smul' c m := by simp [lie_smul, smul_sub]

def IsFiniteTypeMap
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (T : M →ₗ[R] N) : Prop :=
  ∃ (S : Submodule R (M →ₗ[R] N)),
    Module.Finite R S ∧ T ∈ S ∧
    (∀ (x : 𝔤) (f : M →ₗ[R] N), f ∈ S → adjointActionOnHom M N x f ∈ S)

def HomFin
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    Submodule R (M →ₗ[R] N) where
  carrier := { T | IsFiniteTypeMap (𝔤 := 𝔤) M N T }
  add_mem' := by
    intro a b ha hb
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (a + b)
    obtain ⟨S₁, hfin₁, ha_mem, hstab₁⟩ := ha
    obtain ⟨S₂, hfin₂, hb_mem, hstab₂⟩ := hb
    refine ⟨S₁ ⊔ S₂, Submodule.finite_sup S₁ S₂, Submodule.add_mem_sup ha_mem hb_mem, ?_⟩
    intro x f hf
    rw [Submodule.mem_sup] at hf
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := hf
    have : adjointActionOnHom M N x (f₁ + f₂) = adjointActionOnHom M N x f₁ + adjointActionOnHom M N x f₂ := by
      ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
    rw [this]
    exact Submodule.add_mem_sup (hstab₁ x f₁ hf₁) (hstab₂ x f₂ hf₂)
  zero_mem' := by
    show IsFiniteTypeMap (𝔤 := 𝔤) M N 0
    exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun x f hf => by
      rw [Submodule.mem_bot] at hf ⊢
      subst hf
      ext m
      simp [adjointActionOnHom]⟩
  smul_mem' := by
    intro c f hf
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (c • f)
    obtain ⟨S, hfin, hf_mem, hstab⟩ := hf
    exact ⟨S, hfin, S.smul_mem c hf_mem, hstab⟩

def homLeftComp (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    Module.End R N →ₐ[R] Module.End R (M →ₗ[R] N) where
  toFun f := { toFun := fun T => f.comp T
               map_add' := fun T₁ T₂ => by ext; simp
               map_smul' := fun r T => by ext; simp }
  map_one' := by ext T m; simp
  map_mul' := fun f g => by ext T m; simp [Module.End.mul_apply]
  map_zero' := by ext T m; simp
  map_add' := fun f g => by ext T m; simp [LinearMap.add_apply]
  commutes' := fun r => by ext T m; simp [Module.algebraMap_end_apply]

def homRightComp (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    (Module.End R M)ᵐᵒᵖ →ₐ[R] Module.End R (M →ₗ[R] N) where
  toFun gop := { toFun := fun T => T.comp (MulOpposite.unop gop)
                 map_add' := fun T₁ T₂ => by ext; simp
                 map_smul' := fun r T => by ext; simp }
  map_one' := by ext T m; simp
  map_mul' := fun a b => by
    ext T m
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rfl
  map_zero' := by ext T m; simp
  map_add' := fun a b => by ext T m; simp [MulOpposite.unop_add, LinearMap.add_apply]
  commutes' := fun r => by
    ext T m
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Module.algebraMap_end_apply]
    simp [map_smul]

def HomBimodule
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    LieBimodule R 𝔤 where
  carrier := M →ₗ[R] N
  leftAction :=
    (homLeftComp M N).comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N))
  rightAction :=
    (homRightComp M N).comp
      (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)))
  actions_commute := fun u v T => by


    show (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp
        (T.comp (MulOpposite.unop (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)) v))) =
      ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T).comp
        (MulOpposite.unop (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)) v))
    ext m
    simp [LinearMap.comp_apply]

end
