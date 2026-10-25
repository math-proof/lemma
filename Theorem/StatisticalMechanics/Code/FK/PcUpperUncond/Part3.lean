/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.FK.PcUpperUncond.Part3
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


@[simp] lemma fkPcRatio_def (d : ℕ) (p : ℝ) : fkPcRatio d p = (2 * d : ℝ) * (1 - p) := rfl


lemma fkPcSummand_eq (d : ℕ) (p : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ = (ℓ : ℝ) * (fkPcRatio d p) ^ ℓ := by
  rw [fkPcRatio_def, mul_assoc, ← mul_pow]


lemma fkPcUpperBound_eq_closedForm (d : ℕ) (p : ℝ) (hx : ‖fkPcRatio d p‖ < 1) :
    fkPcUpperBound d p = (fkPcRatio d p) / (1 - fkPcRatio d p) ^ 2 := by
  unfold fkPcUpperBound
  rw [show (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ)
        = (fun ℓ : ℕ => (ℓ : ℝ) * (fkPcRatio d p) ^ ℓ) from funext (fkPcSummand_eq d p)]
  exact tsum_coe_mul_geometric_of_norm_lt_one hx


lemma fkPcRatio_tendsto_one (d : ℕ) :
    Tendsto (fun p : ℝ => fkPcRatio d p) (nhds 1) (nhds 0) := by
  have h : Tendsto (fun p : ℝ => fkPcRatio d p) (nhds 1) (nhds ((2 * d : ℝ) * (1 - 1))) := by
    unfold fkPcRatio
    exact (((tendsto_id).const_sub 1).const_mul (2 * d : ℝ))
  simpa using h


lemma fkPcClosedForm_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
  have : Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds (0 / (1 - 0) ^ 2)) := by
    apply Tendsto.div tendsto_id (Continuous.tendsto (by fun_prop) 0)
    norm_num
  simpa using this


lemma fkPcUpperBound_tendsto_one (d : ℕ) :
    Tendsto (fun p : ℝ => fkPcUpperBound d p) (nhds 1) (nhds 0) := by
  have hev : (fun p : ℝ => fkPcUpperBound d p) =ᶠ[nhds 1]
      (fun p : ℝ => (fkPcRatio d p) / (1 - fkPcRatio d p) ^ 2) := by
    have hlt : ∀ᶠ p in nhds 1, ‖fkPcRatio d p‖ < 1 := by
      have hsmall := (fkPcRatio_tendsto_one d).eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
      have hgt : ∀ᶠ p in nhds 1, (-1 : ℝ) < fkPcRatio d p :=
        (fkPcRatio_tendsto_one d).eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))
      filter_upwards [hsmall, hgt] with p hp hp'
      rw [Real.norm_eq_abs, abs_lt]; exact ⟨hp', hp⟩
    filter_upwards [hlt] with p hp
    exact fkPcUpperBound_eq_closedForm d p hp
  rw [tendsto_congr' hev]
  simpa using fkPcClosedForm_tendsto_zero.comp (fkPcRatio_tendsto_one d)


theorem exists_p_lt_one_fkPcUpperBound_lt_one (d : ℕ) :
    ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ < p → p ≤ 1 → fkPcUpperBound d p < 1 := by
  have h : ∀ᶠ p in nhds 1, fkPcUpperBound d p < 1 :=
    (fkPcUpperBound_tendsto_one d).eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hfn⟩ := h
  refine ⟨1 - ε / 2, by linarith, fun p hp1 _ => ?_⟩
  apply hfn
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith


lemma fkPcUpperBound_nonneg (d : ℕ) {p : ℝ} (hp : p ≤ 1) : 0 ≤ fkPcUpperBound d p := by
  unfold fkPcUpperBound
  apply tsum_nonneg
  intro ℓ
  have : (0 : ℝ) ≤ 1 - p := by linarith
  positivity


end FK
end StatMech
