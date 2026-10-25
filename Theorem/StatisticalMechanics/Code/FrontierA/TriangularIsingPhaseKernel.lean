/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbolBounds
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part12
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingSymbol_pos_of_nonnegative_noncritical
    {beta J : Real} (hbeta : 0 < beta) (hJ : 0 <= J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (p q : Real) :
    0 < triangularIsingSymbol beta beta (beta * J) p q := by
  have hzeroNe : triangularIsingSymbol beta beta (beta * J) 0 0 ≠ 0 := by
    intro hzero
    exact hcrit ((triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).1 hzero)
  have hzeroNonneg : 0 <= triangularIsingSymbol beta beta (beta * J) 0 0 := by
    rw [triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul]
    positivity
  have hzeroPos : 0 < triangularIsingSymbol beta beta (beta * J) 0 0 :=
    lt_of_le_of_ne hzeroNonneg (Ne.symm hzeroNe)
  have hs : 0 <= Real.sinh (2 * beta) :=
    (Real.sinh_pos_iff.mpr (by linarith)).le
  have hr : 0 <= Real.sinh (2 * (beta * J)) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hA : 0 <= (1 - Real.cos p) + (1 - Real.cos q) := by
    nlinarith [Real.cos_le_one p, Real.cos_le_one q]
  have hB : 0 <= 1 - Real.cos (p + q) := by
    linarith [Real.cos_le_one (p + q)]
  have hexcess := triangularIsingSymbol_sub_zero beta (beta * J) p q
  have hexcessNonneg : 0 <=
      triangularIsingSymbol beta beta (beta * J) p q -
        triangularIsingSymbol beta beta (beta * J) 0 0 := by
    rw [hexcess]
    positivity
  linarith

theorem triangularIsing_logSymbol_analyticAt_of_nonnegative_noncritical
    {beta J : Real} (hbeta : 0 < beta) (hJ : 0 <= J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (p q : Real) :
    AnalyticAt Real
      (fun b : Real =>
        Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
  apply AnalyticAt.log (by unfold triangularIsingSymbol; fun_prop)
  exact triangularIsingSymbol_pos_of_nonnegative_noncritical
    hbeta hJ hcrit p q


theorem triangularIsing_logSymbol_analyticAt_of_le_neg_one
    {beta J : Real} (hbeta : 0 < beta) (hJ : J <= -1)
    (p q : Real) :
    AnalyticAt Real
      (fun b : Real =>
        Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
  apply AnalyticAt.log (by unfold triangularIsingSymbol; fun_prop)
  apply triangularIsingSymbol_pos_of_third_le_neg hbeta
  nlinarith [mul_le_mul_of_nonneg_left hJ hbeta.le]


theorem triangularIsingSymbol_pos_at_root_of_ne_zero
    {beta J p q : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hp : |p| <= Real.pi) (hq : |q| <= Real.pi)
    (hne : p ≠ 0 ∨ q ≠ 0) :
    0 < triangularIsingSymbol beta beta (beta * J) p q := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_triangularIsingSymbol_quadratic_lower_at_root hbeta hroot
  have hpq : 0 < p ^ 2 + q ^ 2 := by
    rcases hne with hp0 | hq0
    · nlinarith [sq_pos_of_ne_zero hp0]
    · nlinarith [sq_pos_of_ne_zero hq0]
  exact (mul_pos hc hpq).trans_le (hlower p q hp hq)


theorem triangularIsing_logSymbol_analyticAt_at_root_of_ne_zero
    {beta J p q : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hp : |p| <= Real.pi) (hq : |q| <= Real.pi)
    (hne : p ≠ 0 ∨ q ≠ 0) :
    AnalyticAt Real
      (fun b : Real =>
        Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
  apply AnalyticAt.log (by unfold triangularIsingSymbol; fun_prop)
  exact triangularIsingSymbol_pos_at_root_of_ne_zero
    hbeta hroot hp hq hne


theorem triangularIsingSymbol_quadratic_upper_at_root
    {beta J p q : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    triangularIsingSymbol beta beta (beta * J) p q <=
      (Real.sinh (2 * beta) / 2 +
          |Real.sinh (2 * (beta * J))|) * (p ^ 2 + q ^ 2) := by
  let s := Real.sinh (2 * beta)
  let r := Real.sinh (2 * (beta * J))
  let A := (1 - Real.cos p) + (1 - Real.cos q)
  let B := 1 - Real.cos (p + q)
  have hs : 0 <= s := (Real.sinh_pos_iff.mpr (by linarith)).le
  have hA : A <= (p ^ 2 + q ^ 2) / 2 := by
    dsimp [A]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := p),
      Real.one_sub_sq_div_two_le_cos (x := q)]
  have hB0 : 0 <= B := by
    dsimp [B]
    linarith [Real.cos_le_one (p + q)]
  have hB : B <= (p + q) ^ 2 / 2 := by
    dsimp [B]
    linarith [Real.one_sub_sq_div_two_le_cos (x := p + q)]
  have hpq : (p + q) ^ 2 <= 2 * (p ^ 2 + q ^ 2) := by
    nlinarith [sq_nonneg (p - q)]
  have hzero : triangularIsingSymbol beta beta (beta * J) 0 0 = 0 :=
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).2 hroot
  have hexcess := triangularIsingSymbol_sub_zero beta (beta * J) p q
  change triangularIsingSymbol beta beta (beta * J) p q -
      triangularIsingSymbol beta beta (beta * J) 0 0 = s * A + r * B at hexcess
  rw [hzero, sub_zero] at hexcess
  rw [hexcess]
  have hSA : s * A <= s * ((p ^ 2 + q ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left hA hs
  have hrB : r * B <= |r| * B :=
    mul_le_mul_of_nonneg_right (le_abs_self r) hB0
  have habs : 0 <= |r| := abs_nonneg r
  have hrB' : r * B <= |r| * (p ^ 2 + q ^ 2) := by
    calc
      r * B <= |r| * B := hrB
      _ <= |r| * ((p + q) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hB habs
      _ <= |r| * (p ^ 2 + q ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hpq habs]
  dsimp [s, r] at hSA hrB' ⊢
  nlinarith

theorem triangularIsingCriticalUpperCoefficient_pos
    {beta J : Real} (hbeta : 0 < beta) :
    0 < Real.sinh (2 * beta) / 2 +
      |Real.sinh (2 * (beta * J))| := by
  have hs : 0 < Real.sinh (2 * beta) :=
    Real.sinh_pos_iff.mpr (by linarith)
  positivity


end
end StatMech.FrontierA
