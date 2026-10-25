/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

theorem hclib_jensen_two_point {r t : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (ht : |t| ≤ 1) :
    ((1 + t) ^ r + (1 - t) ^ r) / 2 ≤ (1 + t ^ 2) ^ (r / 2) := by
  rw [abs_le] at ht
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  have h2 : (0 : ℝ) ≤ 1 - t := by linarith
  have hconc := concaveOn_rpow (p := r / 2) (by linarith) (by linarith)
  have hmem1 : ((1 + t) ^ 2 : ℝ) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; positivity
  have hmem2 : ((1 - t) ^ 2 : ℝ) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; positivity
  have hJ := hconc.2 hmem1 hmem2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hJ
  have e1 : ((1 + t) ^ 2 : ℝ) ^ (r / 2) = (1 + t) ^ r := by
    rw [← Real.rpow_natCast (1 + t) 2, ← Real.rpow_mul h1]; congr 1; ring
  have e2 : ((1 - t) ^ 2 : ℝ) ^ (r / 2) = (1 - t) ^ r := by
    rw [← Real.rpow_natCast (1 - t) 2, ← Real.rpow_mul h2]; congr 1; ring
  have e3 : ((1 : ℝ) / 2 * (1 + t) ^ 2 + 1 / 2 * (1 - t) ^ 2) = 1 + t ^ 2 := by ring
  rw [e1, e2, e3] at hJ
  linarith


end StatMech.Probability
