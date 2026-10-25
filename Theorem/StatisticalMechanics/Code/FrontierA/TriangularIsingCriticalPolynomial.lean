/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial


namespace StatMech.FrontierA

theorem triangularIsingHighTempSymbol_zero_eq_criticalPolynomial_sq
    (x y : ℝ) :
    triangularIsingHighTempSymbol x x y 0 0 =
      triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) ^ 2 := by
  simp [triangularIsingHighTempSymbol, triangularIsingCriticalPolynomial]
  ring


theorem triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul
    (x y : ℝ) :
    triangularIsingSymbol x x y 0 0 =
      triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) ^ 2 *
        (Real.cosh x ^ 4 * Real.cosh y ^ 2) := by
  have h := triangularIsingHighTempSymbol_mul_cosh_sq x x y 0 0
  rw [triangularIsingHighTempSymbol_zero_eq_criticalPolynomial_sq] at h
  calc
    triangularIsingSymbol x x y 0 0 =
        triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) ^ 2 *
          (Real.cosh x ^ 2 * Real.cosh x ^ 2 * Real.cosh y ^ 2) := h.symm
    _ = _ := by ring


theorem triangularIsingSymbol_zero_iff_criticalPolynomial_zero
    (x y : ℝ) :
    triangularIsingSymbol x x y 0 0 = 0 ↔
      triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) = 0 := by
  rw [triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul]
  have hcosh : Real.cosh x ^ 4 * Real.cosh y ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Real.cosh_pos x).ne')
      (pow_ne_zero _ (Real.cosh_pos y).ne')
  rw [mul_eq_zero, or_iff_left hcosh, sq_eq_zero_iff]


theorem triangularIsingCriticalPolynomial_eq_zero_iff
    {t r : ℝ} (hden : 1 + 2 * t - t ^ 2 ≠ 0) :
    triangularIsingCriticalPolynomial t r = 0 ↔
      r = (1 - 2 * t - t ^ 2) / (1 + 2 * t - t ^ 2) := by
  unfold triangularIsingCriticalPolynomial
  constructor
  · intro h
    apply (eq_div_iff hden).2
    linarith
  · intro h
    apply (eq_div_iff hden).1 at h
    linarith


end StatMech.FrontierA
