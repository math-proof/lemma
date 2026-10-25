/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BKKKLTruncation.Part2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bkt2_capped_levelGe2_damped [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  
  have hfull := lib_capped_optimal_weight hp0 hp1 φ hu0 hu1
  
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  have hsub : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * ∑ S : Finset ι, (S.card : ℝ)
          * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro S _ _
    have : (0 : ℝ) ≤ ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) := by positivity
    positivity
  exact le_trans hsub hfull


theorem bkt2_damped_le_target {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu1 : u < 1)
    (d : ℕ) :
    ((1 - u) * (4 * p * (1 - p))) ^ (d - 1) ≤ (1 - u) ^ (d - 1) := by
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  have hs0 : (0 : ℝ) ≤ 4 * p * (1 - p) := by nlinarith
  have hs1 : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [hs1, h1u0]


theorem bkt2_target_eq_damped_of_p_half {u : ℝ} (d : ℕ) :
    (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = (1 - u) ^ (d - 1) := by
  norm_num


end StatMech.Probability
