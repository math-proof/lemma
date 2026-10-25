/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part2
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingRayGap_pos
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    0 < triangularIsingRayGap beta J := by
  by_cases hJnonneg : 0 <= J
  · simp only [triangularIsingRayGap, if_pos hJnonneg]
    exact triangularIsingSymbol_pos_of_nonnegative_noncritical
      hbeta hJnonneg hcrit 0 0
  · have hJneg : J < 0 := lt_of_not_ge hJnonneg
    by_cases hbranch : 0 <= Real.sinh (2 * beta) +
        2 * Real.sinh (2 * (beta * J))
    · simp only [triangularIsingRayGap, if_neg hJnonneg, if_pos hbranch]
      have hzeroNe : triangularIsingSymbol beta beta (beta * J) 0 0 ≠ 0 := by
        intro hzero
        exact hcrit
          ((triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).1 hzero)
      have hzeroNonneg :
          0 <= triangularIsingSymbol beta beta (beta * J) 0 0 := by
        rw [triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul]
        positivity
      exact lt_of_le_of_ne hzeroNonneg (Ne.symm hzeroNe)
    · simp only [triangularIsingRayGap, if_neg hJnonneg, if_neg hbranch]
      apply triangular_hyperbolic_lower_pos_of_weak_neg_large
      · positivity
      · have hbJ : beta * J < 0 := mul_neg_of_pos_of_neg hbeta hJneg
        exact by linarith
      · linarith

theorem triangularIsingRayGap_le_symbol
    {beta J : Real} (hbeta : 0 < beta)
    (p q : Real) :
    triangularIsingRayGap beta J <=
      triangularIsingSymbol beta beta (beta * J) p q := by
  by_cases hJnonneg : 0 <= J
  · simp only [triangularIsingRayGap, if_pos hJnonneg]
    have hs : 0 <= Real.sinh (2 * beta) :=
      (Real.sinh_pos_iff.mpr (by linarith)).le
    have hr : 0 <= Real.sinh (2 * (beta * J)) :=
      Real.sinh_nonneg_iff.mpr (by positivity)
    have hA : 0 <= (1 - Real.cos p) + (1 - Real.cos q) := by
      nlinarith [Real.cos_le_one p, Real.cos_le_one q]
    have hB : 0 <= 1 - Real.cos (p + q) := by
      linarith [Real.cos_le_one (p + q)]
    have h := triangularIsingSymbol_sub_zero beta (beta * J) p q
    nlinarith [mul_nonneg hs hA, mul_nonneg hr hB]
  · have hJneg : J < 0 := lt_of_not_ge hJnonneg
    have hr : Real.sinh (2 * (beta * J)) < 0 := by
      apply Real.sinh_neg_iff.mpr
      have hbJ : beta * J < 0 := mul_neg_of_pos_of_neg hbeta hJneg
      linarith
    by_cases hbranch : 0 <= Real.sinh (2 * beta) +
        2 * Real.sinh (2 * (beta * J))
    · simp only [triangularIsingRayGap, if_neg hJnonneg, if_pos hbranch]
      have htrig := triangular_cosine_combination_le_zero_of_sum_nonneg
        hr hbranch p q
      unfold triangularIsingSymbol
      simp only [Real.cos_zero, zero_add, mul_one]
      nlinarith
    · simp only [triangularIsingRayGap, if_neg hJnonneg, if_neg hbranch]
      exact triangularIsingSymbol_equal_couplings_lower
        hbeta (mul_neg_of_pos_of_neg hbeta hJneg) p q


end
end StatMech.FrontierA
