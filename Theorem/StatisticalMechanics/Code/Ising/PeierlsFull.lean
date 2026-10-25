/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Ising.Peierls.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Ising.PeierlsFull
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


@[simp] lemma peierlsRatio_def (d : ℕ) (β : ℝ) :
    peierlsRatio d β = (2 * d : ℝ) * Real.exp (-(2 * β)) := rfl


lemma peierlsRatio_nonneg (d : ℕ) (β : ℝ) : 0 ≤ peierlsRatio d β := by
  unfold peierlsRatio; positivity


lemma peierlsSummand_eq (d : ℕ) (β : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ)
      = (ℓ : ℝ) * (peierlsRatio d β) ^ ℓ := by
  rw [peierlsRatio_def, mul_assoc]
  congr 1
  conv_rhs => rw [mul_pow, ← Real.exp_nat_mul]
  rw [mul_comm (ℓ : ℝ) (-(2 * β))]


lemma peierlsBound_eq_closedForm (d : ℕ) (β : ℝ)
    (hx : ‖peierlsRatio d β‖ < 1) :
    peierlsBound d β = (peierlsRatio d β) / (1 - peierlsRatio d β) ^ 2 := by
  unfold peierlsBound
  rw [show (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ))
        = (fun ℓ : ℕ => (ℓ : ℝ) * (peierlsRatio d β) ^ ℓ) from
      funext (peierlsSummand_eq d β)]
  exact tsum_coe_mul_geometric_of_norm_lt_one hx


lemma peierlsRatio_tendsto_atTop (d : ℕ) :
    Tendsto (fun β : ℝ => peierlsRatio d β) atTop (nhds 0) := by
  have h1 : Tendsto (fun β : ℝ => Real.exp (-(2 * β))) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_atBot.2
    intro b
    filter_upwards [eventually_ge_atTop (-b / 2)] with β hβ
    nlinarith
  have := h1.const_mul (2 * d : ℝ)
  simpa [peierlsRatio] using this


lemma closedForm_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
  have : Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds (0 / (1 - 0) ^ 2)) := by
    apply Tendsto.div tendsto_id (Continuous.tendsto (by fun_prop) 0)
    norm_num
  simpa using this


lemma peierlsBound_tendsto_atTop (d : ℕ) :
    Tendsto (fun β : ℝ => peierlsBound d β) atTop (nhds 0) := by
  have hev : (fun β : ℝ => peierlsBound d β) =ᶠ[atTop]
      (fun β : ℝ => (peierlsRatio d β) / (1 - peierlsRatio d β) ^ 2) := by
    have hlt : ∀ᶠ β in atTop, peierlsRatio d β < 1 :=
      (peierlsRatio_tendsto_atTop d).eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hlt] with β hβ
    refine peierlsBound_eq_closedForm d β ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (peierlsRatio_nonneg d β)]
    exact hβ
  rw [tendsto_congr' hev]
  simpa using closedForm_tendsto_zero.comp (peierlsRatio_tendsto_atTop d)


theorem exists_beta_peierlsBound_lt_half (d : ℕ) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → peierlsBound d β < 1 / 2 := by
  have h := (peierlsBound_tendsto_atTop d).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  rw [eventually_atTop] at h
  obtain ⟨β₀, hβ₀⟩ := h
  exact ⟨β₀, hβ₀⟩


lemma peierlsBound_nonneg (d : ℕ) (β : ℝ) : 0 ≤ peierlsBound d β := by
  unfold peierlsBound
  apply tsum_nonneg
  intro ℓ
  positivity


lemma contour_card_le (d : ℕ) (B : Finset (Site d)) (ℓ : ℕ) (hB : B.card ≤ ℓ) :
    ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℝ)
      ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by
  have h1 := card_circuits_based_in_le_pow d B ℓ
  have h3 : ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℕ)
      ≤ ℓ * (2 * d) ^ ℓ := le_trans h1 (Nat.mul_le_mul_right _ hB)
  calc ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℝ)
      ≤ ((ℓ * (2 * d) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast h3
    _ = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by push_cast; ring


lemma contour_card_le_peierlsSummand (d : ℕ) (β : ℝ) (B : Finset (Site d)) (ℓ : ℕ)
    (hB : B.card ≤ ℓ) :
    ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℝ)
        * Real.exp (-(2 * β) * ℓ)
      ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ) := by
  apply mul_le_mul_of_nonneg_right (contour_card_le d B ℓ hB) (le_of_lt (Real.exp_pos _))


end Ising
end StatMech
