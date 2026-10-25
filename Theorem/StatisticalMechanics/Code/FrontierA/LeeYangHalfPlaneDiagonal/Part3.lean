/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
import Def.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part2
open Filter Metric Set Topology
open scoped UniformConvergence


namespace StatMech.FrontierA

open StatMech.FK


theorem leftHalfPlaneCompact_isCompact (n : ℕ) :
    IsCompact (leftHalfPlaneCompact n) := by
  apply (isCompact_closedBall (0 : ℂ) (n + 1 : ℝ)).inter_right
  exact isClosed_le Complex.continuous_re continuous_const

theorem leftHalfPlaneCompact_subset (n : ℕ) :
    leftHalfPlaneCompact n ⊆ {z : ℂ | z.re < 0} := by
  intro z hz
  have hden : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  exact hz.2.trans_lt (neg_neg_of_pos (div_pos zero_lt_one hden))

theorem leftHalfPlaneCompact_cofinal
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ {z : ℂ | z.re < 0}) :
    ∃ n, K ⊆ leftHalfPlaneCompact n := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨z₀, hz₀K, hz₀max⟩ :=
    hK.exists_isMaxOn hKne Complex.continuous_re.continuousOn
  have hz₀neg : z₀.re < 0 := hKU hz₀K
  have hdelta : 0 < -z₀.re := neg_pos.mpr hz₀neg
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt (max C (1 / (-z₀.re)))
  refine ⟨n, fun z hz => ⟨?_, ?_⟩⟩
  · rw [mem_closedBall, dist_zero_right]
    have hnorm : ‖z‖ ≤ C := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hC z hz
    exact hnorm.trans ((le_max_left C (1 / (-z₀.re))).trans hn.le |>.trans (by norm_num))
  · have hrecip : (1 : ℝ) / (n + 1) ≤ -z₀.re := by
      rw [one_div_le (by positivity) hdelta]
      exact ((le_max_right C (1 / (-z₀.re))).trans hn.le).trans (by norm_num)
    have hzmax : z.re ≤ z₀.re := isMaxOn_iff.mp hz₀max z hz
    exact hzmax.trans (by simpa only [neg_neg] using neg_le_neg hrecip)


end StatMech.FrontierA
