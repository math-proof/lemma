/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryOII.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Lemma.Int.IsInQPlus0
import Lemma.Int.Surjective_Comp.of.Surjective
import Def.v1.Atlas.LieGroups.code.TensorHomAxiom
import Def.v1.Atlas.LieGroups.code.CategoryOII


noncomputable section

open Classical

universe uCatO

universe u_V u_M u_P

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

theorem verma_module_isCategoryO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hM : IsVermaModule Δ M wt) :
    IsCategoryO Δ rd M := by
  constructor
  ·
    refine ⟨{_hM.highestWeightVec}, ?_⟩
    simp only [Finset.coe_singleton]
    exact _hM.toIsHighestWeightModule.generates
  ·
    have hwd := _hM.toIsHighestWeightModule.weight_decomposition
    intro m
    have hm : m ∈ (⨆ (μ : Δ.𝔥 →ₗ[R] R), Δ.weightSubspace M μ : Submodule R M) := by
      rw [hwd]; exact Submodule.mem_top
    rw [Submodule.mem_iSup_iff_exists_finset] at hm
    obtain ⟨s, hms⟩ := hm
    rw [Submodule.mem_iSup_finset_iff_exists_sum] at hms
    obtain ⟨v, hv⟩ := hms
    exact ⟨s, fun μ => ⟨(v μ : M), (v μ).prop⟩, hv.symm⟩
  ·
    exact ⟨{wt}, fun μ hμ => ⟨wt, Finset.mem_singleton.mpr rfl,
      _hM.weight_subset_QPlus rd μ hμ⟩⟩


end
