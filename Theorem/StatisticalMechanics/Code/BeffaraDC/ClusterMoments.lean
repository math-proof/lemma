/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.ClusterMoments
open scoped BigOperators
open Set Filter Topology


namespace StatMech

namespace BeffaraDC

theorem summable_pow_mul_of_geometricTail {dist : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hnn : ∀ n, 0 ≤ dist n) (htail : ∀ n, dist n ≤ C * r ^ n)
    (d : ℕ) : Summable (fun n : ℕ => (n : ℝ) ^ d * dist n) := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ d * (C * r ^ n)) := by
    have h := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d
      (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left C
    exact h.congr (fun n => by ring)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeo
  · exact mul_nonneg (by positivity) (hnn n)
  · exact mul_le_mul_of_nonneg_left (htail n) (by positivity)


theorem clusterMoment_summand_summable {dist : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hnn : ∀ n, 0 ≤ dist n) (htail : ∀ n, dist n ≤ C * r ^ n)
    (d : ℕ) : Summable (fun n : ℕ => (n : ℝ) ^ d * dist n) :=
  summable_pow_mul_of_geometricTail hr0 hr1 hnn htail d


theorem clusterMoment_nonneg {dist : ℕ → ℝ} (hnn : ∀ n, 0 ≤ dist n) (d : ℕ) :
    0 ≤ clusterMoment dist d :=
  tsum_nonneg (fun n => mul_nonneg (by positivity) (hnn n))


theorem clusterMoment_le_of_geometricTail {dist : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hnn : ∀ n, 0 ≤ dist n) (htail : ∀ n, dist n ≤ C * r ^ n)
    (d : ℕ) :
    clusterMoment dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (C * r ^ n) := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ d * (C * r ^ n)) := by
    have h := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d
      (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left C
    exact h.congr (fun n => by ring)
  refine Summable.tsum_mono
    (summable_pow_mul_of_geometricTail hr0 hr1 hnn htail d) hgeo (fun n => ?_)
  exact mul_le_mul_of_nonneg_left (htail n) (by positivity)


end BeffaraDC
end StatMech
