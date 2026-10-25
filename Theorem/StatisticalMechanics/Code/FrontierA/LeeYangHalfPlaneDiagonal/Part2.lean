/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
import Def.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal
open Filter Metric Set Topology
open scoped UniformConvergence


namespace StatMech.FrontierA

open StatMech.FK


theorem rightHalfPlaneCompact_isCompact (n : ℕ) :
    IsCompact (rightHalfPlaneCompact n) := by
  apply (isCompact_closedBall (0 : ℂ) (n + 1 : ℝ)).inter_right
  exact isClosed_le continuous_const Complex.continuous_re

theorem rightHalfPlaneCompact_subset (n : ℕ) :
    rightHalfPlaneCompact n ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  have hden : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  exact (div_pos zero_lt_one hden).trans_le hz.2

theorem rightHalfPlaneCompact_cofinal
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ {z : ℂ | 0 < z.re}) :
    ∃ n, K ⊆ rightHalfPlaneCompact n := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨z₀, hz₀K, hz₀min⟩ :=
    hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  have hz₀pos : 0 < z₀.re := hKU hz₀K
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt (max C (1 / z₀.re))
  refine ⟨n, fun z hz => ⟨?_, ?_⟩⟩
  · rw [mem_closedBall, dist_zero_right]
    have hnorm : ‖z‖ ≤ C := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hC z hz
    exact hnorm.trans ((le_max_left C (1 / z₀.re)).trans hn.le |>.trans (by norm_num))
  · have hrecip : (1 : ℝ) / (n + 1) ≤ z₀.re := by
      rw [one_div_le (by positivity) hz₀pos]
      exact ((le_max_right C (1 / z₀.re)).trans hn.le).trans (by norm_num)
    exact hrecip.trans (isMinOn_iff.mp hz₀min z hz)


end StatMech.FrontierA
