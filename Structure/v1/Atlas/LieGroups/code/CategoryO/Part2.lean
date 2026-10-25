/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Lemma.Int.IsIntegral
import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Instance.v1.Atlas.LieGroups.code.HilbertNoether
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Def.v1.Atlas.LieGroups.code.CategoryO.Part2


noncomputable section

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

section CategoryOResults

variable {Δ : TriangularDecomposition R 𝔤}

variable {rd : PositiveRootData Δ}

variable {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

structure RootSystemWithReflections
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) where
  allRoots : Finset (Δ.𝔥 →ₗ[R] R)
  posRoots_sub : ∀ α ∈ rd.posRoots, α ∈ allRoots
  roots_pos_or_neg : ∀ α ∈ allRoots, α ∈ rd.posRoots ∨ -α ∈ rd.posRoots
  reflection : (Δ.𝔥 →ₗ[R] R) → wg.W
  coroot : (Δ.𝔥 →ₗ[R] R) → Δ.𝔥
  corootPairing_eq_eval : ∀ α ∈ allRoots, ∀ μ : Δ.𝔥 →ₗ[R] R,
    rd.corootPairing μ α = μ (coroot α)
  reflection_formula : ∀ α ∈ allRoots, ∀ μ : Δ.𝔥 →ₗ[R] R,
    wg.dualAction (reflection α) μ = μ - (μ (coroot α)) • α
  reflection_order_two : ∀ α ∈ allRoots, reflection α * reflection α = 1
  allRoots_neg_closed : ∀ α ∈ allRoots, -α ∈ allRoots
  reflection_neg : ∀ α ∈ allRoots, reflection (-α) = reflection α
  reflection_conjugation : ∀ α ∈ allRoots, ∀ β ∈ allRoots,
    reflection α * reflection β * reflection α =
    reflection (wg.dualAction (reflection α) β)
  allRoots_reflection_closed : ∀ α ∈ allRoots, ∀ β ∈ allRoots,
    wg.dualAction (reflection α) β ∈ allRoots
  dualAction_sub : ∀ (w : wg.W) (μ ν : Δ.𝔥 →ₗ[R] R),
    wg.dualAction w (μ - ν) = wg.dualAction w μ - wg.dualAction w ν
  dualAction_zsmul : ∀ (w : wg.W) (n : ℤ) (μ : Δ.𝔥 →ₗ[R] R),
    wg.dualAction w (n • μ) = n • wg.dualAction w μ
  dualAction_rootLattice : ∀ (w : wg.W) (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    ∃ (c' : (Δ.𝔥 →ₗ[R] R) → ℤ),
      wg.dualAction w (∑ α ∈ rd.posRoots, c α • α) = ∑ α ∈ rd.posRoots, c' α • α
  pairing_integral : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ allRoots →
    ∀ (μ : Δ.𝔥 →ₗ[R] R),
    (∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
      -(μ (coroot α)) • α = ∑ γ ∈ rd.posRoots, c γ • γ) →
    ∃ (n : ℤ), μ (coroot α) = (n : R)
  generated_by_reflections : ∀ w : wg.W, ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
    (∀ i, αs i ∈ allRoots) ∧
    w = (List.ofFn (fun i => reflection (αs i))).prod
  ρ_eq_half_sum : (2 : R) • wg.ρ = rd.sumPosRoots

end CategoryOResults
end
