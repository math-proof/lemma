/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial.Part2


namespace StatMech.FrontierA

theorem triangularIsingCriticalCompanion_pos
    {t r : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hr0 : -1 < r) (hr1 : r < 1) :
    0 < triangularIsingCriticalCompanion t r := by
  unfold triangularIsingCriticalCompanion
  have htsq : t ^ 2 < 1 := by nlinarith [sq_nonneg (1 - t)]
  by_cases hA : 0 ≤ 1 - 2 * t - t ^ 2
  · have hm := mul_le_mul_of_nonneg_left (le_of_lt hr0) hA
    nlinarith
  · have hm := mul_lt_mul_of_neg_left hr1 (lt_of_not_ge hA)
    nlinarith


theorem sinh_two_mul_eq_two_tanh_div (x : ℝ) :
    Real.sinh (2 * x) =
      2 * Real.tanh x / (1 - Real.tanh x ^ 2) := by
  rw [Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hcs := Real.cosh_sq_sub_sinh_sq x
  field_simp [hc]
  linear_combination Real.sinh x * hcs


end StatMech.FrontierA
