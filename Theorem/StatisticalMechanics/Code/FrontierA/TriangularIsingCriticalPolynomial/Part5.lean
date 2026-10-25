/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial.Part5


namespace StatMech.FrontierA

theorem hasDerivAt_triangularIsingCriticalRateAlong (β J : ℝ) :
    HasDerivAt (fun b : ℝ => triangularIsingCriticalRate b (b * J))
      (triangularIsingCriticalRateAlongDeriv β J) β := by
  have hx : HasDerivAt (fun b : ℝ => 2 * b) 2 β := by
    convert (hasDerivAt_id β).const_mul 2 using 1 <;> ring
  have hy : HasDerivAt (fun b : ℝ => 2 * (b * J)) (2 * J) β := by
    convert ((hasDerivAt_id β).mul_const J).const_mul 2 using 1 <;> ring
  have hs : HasDerivAt (fun b : ℝ => Real.sinh (2 * b))
      (2 * Real.cosh (2 * β)) β := by
    convert (Real.hasDerivAt_sinh (2 * β)).comp β hx using 1 <;> ring
  have hr : HasDerivAt (fun b : ℝ => Real.sinh (2 * (b * J)))
      (2 * J * Real.cosh (2 * (β * J))) β := by
    convert (Real.hasDerivAt_sinh (2 * (β * J))).comp β hy using 1 <;> ring
  have h := (hs.pow 2).add ((hs.mul hr).const_mul 2)
  convert h using 1
  · ext b
    simp only [triangularIsingCriticalRate, Pi.pow_apply, Pi.add_apply,
      Pi.mul_apply]
    ring
  · simp only [triangularIsingCriticalRateAlongDeriv]
    ring


theorem triangularIsingCriticalRateAlongDeriv_pos_at_root
    {β J : ℝ} (hβ : 0 < β) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate β (β * J) = 1) :
    0 < triangularIsingCriticalRateAlongDeriv β J := by
  by_cases hnonneg : 0 ≤ J
  · have hs : 0 < Real.sinh (2 * β) := Real.sinh_pos_iff.mpr (by linarith)
    have hr : 0 ≤ Real.sinh (2 * (β * J)) :=
      Real.sinh_nonneg_iff.mpr (by positivity)
    have hc : 0 < Real.cosh (2 * β) := Real.cosh_pos _
    have hcr : 0 < Real.cosh (2 * (β * J)) := Real.cosh_pos _
    unfold triangularIsingCriticalRateAlongDeriv
    positivity
  · have hJneg : J < 0 := lt_of_not_ge hnonneg
    let a := -J
    let x := 2 * β
    let s := Real.sinh x
    let q := Real.sinh (a * x)
    have ha0 : 0 < a := by dsimp [a]; linarith
    have ha1 : a < 1 := by dsimp [a]; linarith
    have hx : 0 < x := by dsimp [x]; linarith
    have hs : 0 < s := Real.sinh_pos_iff.mpr hx
    have hy : 2 * (β * J) = -(a * x) := by dsimp [a, x]; ring
    have hprod : s * (s - 2 * q) = 1 := by
      rw [triangularIsingCriticalRate, hy, Real.sinh_neg] at hroot
      change s ^ 2 + 2 * s * -q = 1 at hroot
      nlinarith
    have hd : 0 < s - 2 * q := by
      have hp : 0 < s * (s - 2 * q) := by rw [hprod]; norm_num
      rcases mul_pos_iff.mp hp with h | h
      · exact h.2
      · exact (lt_asymm hs h.1).elim
    have hnum : 0 < Real.cosh x * q -
        a * s * Real.cosh (a * x) := by
      exact sinh_scale_ratio_derivNumerator_pos ha0 ha1 hx
    have hmain : 0 < Real.cosh x * (s - 2 * q) :=
      mul_pos (Real.cosh_pos x) hd
    rw [triangularIsingCriticalRateAlongDeriv, show 2 * β = x by rfl,
      hy, Real.sinh_neg, Real.cosh_neg]
    change 0 < 4 * s * Real.cosh x + 4 * Real.cosh x * -q +
      4 * J * s * Real.cosh (a * x)
    dsimp [a] at hnum
    nlinarith

end StatMech.FrontierA
