/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Def.StatisticalMechanics.Code.Percolation.PcUpper
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


@[simp] lemma pcRatio_def (p : ℝ) : pcRatio p = 4 * (1 - p) := rfl


lemma pcSummand_eq (p : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ = (ℓ : ℝ) * (pcRatio p) ^ ℓ := by
  rw [pcRatio_def, mul_assoc, ← mul_pow]


lemma pcUpperBound_eq_closedForm (p : ℝ) (hx : ‖pcRatio p‖ < 1) :
    pcUpperBound p = (pcRatio p) / (1 - pcRatio p) ^ 2 := by
  unfold pcUpperBound
  rw [show (fun ℓ : ℕ => (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ)
        = (fun ℓ : ℕ => (ℓ : ℝ) * (pcRatio p) ^ ℓ) from funext (pcSummand_eq p)]
  exact tsum_coe_mul_geometric_of_norm_lt_one hx


lemma pcRatio_tendsto_one : Tendsto (fun p : ℝ => pcRatio p) (nhds 1) (nhds 0) := by
  have h : Tendsto (fun p : ℝ => pcRatio p) (nhds 1) (nhds (4 * (1 - 1))) := by
    unfold pcRatio
    exact (((tendsto_id).const_sub 1).const_mul 4)
  simpa using h


lemma pcClosedForm_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
  have : Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds (0 / (1 - 0) ^ 2)) := by
    apply Tendsto.div tendsto_id (Continuous.tendsto (by fun_prop) 0)
    norm_num
  simpa using this


lemma pcUpperBound_tendsto_one : Tendsto (fun p : ℝ => pcUpperBound p) (nhds 1) (nhds 0) := by
  have hev : (fun p : ℝ => pcUpperBound p) =ᶠ[nhds 1]
      (fun p : ℝ => (pcRatio p) / (1 - pcRatio p) ^ 2) := by
    have hlt : ∀ᶠ p in nhds 1, ‖pcRatio p‖ < 1 := by
      have := (pcRatio_tendsto_one).eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
      
      have hgt : ∀ᶠ p in nhds 1, (-1 : ℝ) < pcRatio p :=
        (pcRatio_tendsto_one).eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))
      filter_upwards [this, hgt] with p hp hp'
      rw [Real.norm_eq_abs, abs_lt]; exact ⟨hp', hp⟩
    filter_upwards [hlt] with p hp
    exact pcUpperBound_eq_closedForm p hp
  rw [tendsto_congr' hev]
  simpa using pcClosedForm_tendsto_zero.comp (pcRatio_tendsto_one)


theorem exists_p_lt_one_pcUpperBound_lt_one :
    ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ < p → p ≤ 1 → pcUpperBound p < 1 := by
  have h : ∀ᶠ p in nhds 1, pcUpperBound p < 1 :=
    (pcUpperBound_tendsto_one).eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hfn⟩ := h
  refine ⟨1 - ε / 2, by linarith, fun p hp1 _ => ?_⟩
  apply hfn
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith


lemma pcUpperBound_nonneg {p : ℝ} (hp : p ≤ 1) : 0 ≤ pcUpperBound p := by
  unfold pcUpperBound
  apply tsum_nonneg
  intro ℓ
  have : (0 : ℝ) ≤ 1 - p := by linarith
  positivity


lemma pcContour_card_le (B : Finset (Site 2)) (ℓ : ℕ) (hB : B.card ≤ ℓ) :
    ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℝ)
      ≤ (ℓ : ℝ) * (4 : ℝ) ^ ℓ := by
  
  
  have h1 := card_circuits_based_in_le_pow 2 B ℓ
  have h3 : ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℕ)
      ≤ ℓ * (2 * 2) ^ ℓ := le_trans h1 (Nat.mul_le_mul_right _ hB)
  calc ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℝ)
      ≤ ((ℓ * (2 * 2) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast h3
    _ = (ℓ : ℝ) * (4 : ℝ) ^ ℓ := by push_cast; ring


lemma pcContour_card_le_summand {p : ℝ} (hp : p ≤ 1) (B : Finset (Site 2)) (ℓ : ℕ)
    (hB : B.card ≤ ℓ) :
    ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℝ) * (1 - p) ^ ℓ
      ≤ (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ := by
  have hpow : (0 : ℝ) ≤ (1 - p) ^ ℓ := by
    have : (0 : ℝ) ≤ 1 - p := by linarith
    positivity
  exact mul_le_mul_of_nonneg_right (pcContour_card_le B ℓ hB) hpow


end Percolation
end StatMech
