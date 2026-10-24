/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompositionSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.CategoryOII
import Lemma.Int.WeightLE.of.BruhatLE

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

structure LieModule.CompositionSeries
    (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  length : ℕ
  series : Fin (length + 1) → LieSubmodule R 𝔤 M
  bot : series ⟨0, Nat.zero_lt_succ length⟩ = ⊥
  top : series ⟨length, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤
  strictly_mono : ∀ i : Fin length, series i.castSucc < series i.succ

noncomputable def jordanHolder_compMult_raw
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (_wg : WeylGroupData Δ) :
    (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → ℕ := fun lam mu =>


  let h_lam := @verma_module_exists.{0} R _ 𝔤 _ _ Δ lam
  let Mlam := h_lam.choose
  let instACG_M := h_lam.choose_spec.choose
  let instMod_M := h_lam.choose_spec.choose_spec.choose
  let instLRM_M := h_lam.choose_spec.choose_spec.choose_spec.choose
  let instLM_M := h_lam.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let hMlam := h_lam.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some

  let h_mu := @verma_module_exists.{0} R _ 𝔤 _ _ Δ mu
  let Mmu := h_mu.choose
  let instACG_L := h_mu.choose_spec.choose
  let instMod_L := h_mu.choose_spec.choose_spec.choose
  let instLRM_L := h_mu.choose_spec.choose_spec.choose_spec.choose
  let instLM_L := h_mu.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let hMmu := h_mu.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some

  let h_max := hMmu.exists_unique_maximal_submodule
  let J := h_max.choose
  let hJ_ne_top := h_max.choose_spec.1
  let hJ_max := h_max.choose_spec.2

  let hCatO : IsCategoryO Δ rd Mlam :=
    @verma_module_isCategoryO R _ 𝔤 _ _ Δ rd Mlam instACG_M instMod_M instLRM_M instLM_M lam hMlam

  @compositionMultiplicityOfModule R _ 𝔤 _ _ Δ rd
    Mlam instACG_M instMod_M instLRM_M instLM_M hCatO
    (@HasQuotient.Quotient Mmu (LieSubmodule R 𝔤 Mmu) _ J)
    inferInstance inferInstance inferInstance inferInstance
    (@IsVermaModule.quotient_by_maximal_irreducible R _ 𝔤 _ _ Δ Mmu instACG_L instMod_L
      instLRM_L instLM_L mu hMmu J hJ_ne_top hJ_max)

def compositionMultiplicity
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) : ℕ :=
  jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu

end
