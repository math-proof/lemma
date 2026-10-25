/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EllipticFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexAnalysis
import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis.Part3
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Def.v1.Atlas.EllipticCurves.code.EllipticFunction.Part2
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

variable {L}

/-- The poles of an elliptic function in any fundamental parallelogram form a finite
set, because they are a discrete subset of a bounded region (the closure of the
parallelogram is compact). -/
theorem polesInFundParallelogram_finite
    {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) (α : ℂ) :
    Set.Finite (L.polesInFundParallelogram f α) := by
  open Topology Filter in
  by_contra h_inf
  have h_inf' : Set.Infinite (L.polesInFundParallelogram f α) := h_inf

  have h_bdd : Bornology.IsBounded (L.fundamentalParallelogram α) := by
    rw [Metric.isBounded_iff_subset_closedBall α]
    refine ⟨‖L.ω₁‖ + ‖L.ω₂‖, ?_⟩
    intro z hz
    rw [L.mem_fundamentalParallelogram_iff] at hz
    obtain ⟨t₁, t₂, ht₁_nn, ht₁_lt, ht₂_nn, ht₂_lt, rfl⟩ := hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : α + t₁ • L.ω₁ + t₂ • L.ω₂ - α = t₁ • L.ω₁ + t₂ • L.ω₂ := by abel
    rw [hsub]
    have h1 : ‖t₁ • L.ω₁‖ ≤ ‖L.ω₁‖ :=
      calc ‖t₁ • L.ω₁‖ ≤ ‖t₁‖ * ‖L.ω₁‖ := norm_smul_le t₁ L.ω₁
        _ ≤ 1 * ‖L.ω₁‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = ‖L.ω₁‖ := one_mul _
    have h2 : ‖t₂ • L.ω₂‖ ≤ ‖L.ω₂‖ :=
      calc ‖t₂ • L.ω₂‖ ≤ ‖t₂‖ * ‖L.ω₂‖ := norm_smul_le t₂ L.ω₂
        _ ≤ 1 * ‖L.ω₂‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = ‖L.ω₂‖ := one_mul _
    calc ‖t₁ • L.ω₁ + t₂ • L.ω₂‖
        ≤ ‖t₁ • L.ω₁‖ + ‖t₂ • L.ω₂‖ := norm_add_le _ _
      _ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ := add_le_add h1 h2

  have h_compact := h_bdd.isCompact_closure

  have h_sub : L.polesInFundParallelogram f α ⊆ closure (L.fundamentalParallelogram α) := by
    intro z hz
    unfold polesInFundParallelogram at hz
    exact subset_closure (Set.mem_sep_iff.mp hz).1

  obtain ⟨x, -, hx_acc⟩ := h_inf'.exists_accPt_of_subset_isCompact h_compact h_sub

  have h_ev : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ f y := (hf.meromorphic x).eventually_analyticAt

  have h_disj : Disjoint (𝓝[≠] x) (𝓟 (L.polesInFundParallelogram f α)) := by
    rw [disjoint_principal_right]
    apply Filter.mem_of_superset h_ev
    intro y hy hy_mem
    unfold polesInFundParallelogram IsPoleAt at hy_mem
    exact absurd (Set.mem_sep_iff.mp hy_mem).2 (not_lt.mpr hy.meromorphicOrderAt_nonneg)

  exact hx_acc.ne (disjoint_iff.mp h_disj)

end ComplexLattice
end
