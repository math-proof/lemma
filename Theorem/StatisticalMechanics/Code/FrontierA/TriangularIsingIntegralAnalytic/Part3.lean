/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part3
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

theorem continuous_triangularIsingComplexControl (beta J : Real) :
    Continuous (triangularIsingComplexControl beta J) := by
  unfold triangularIsingComplexControl
  fun_prop

theorem triangularIsingComplexControl_ofReal (beta J : Real) :
    triangularIsingComplexControl beta J beta = 0 := by
  have h2 : (2 : Complex) * beta = ((2 * beta : Real) : Complex) := by
    norm_num
  have hJ : ((2 * beta : Real) : Complex) * J =
      ((2 * (beta * J) : Real) : Complex) := by
    norm_num
    ring
  unfold triangularIsingComplexControl
  rw [h2, hJ, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  norm_num

theorem triangularIsingComplexRadius_pos
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    0 < triangularIsingComplexRadius beta J := by
  unfold triangularIsingComplexRadius
  exact lt_min (by positivity [triangularIsingRayGap_pos hbeta hcrit]) zero_lt_one

theorem triangularIsingComplexNeighborhood_isOpen (beta J : Real) :
    IsOpen (triangularIsingComplexNeighborhood beta J) := by
  exact isOpen_lt (continuous_triangularIsingComplexControl beta J) continuous_const

theorem triangularIsingComplexNeighborhood_mem_nhds
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    triangularIsingComplexNeighborhood beta J ∈ nhds (beta : Complex) := by
  apply (triangularIsingComplexNeighborhood_isOpen beta J).mem_nhds
  change triangularIsingComplexControl beta J beta <
    triangularIsingComplexRadius beta J
  rw [triangularIsingComplexControl_ofReal]
  exact triangularIsingComplexRadius_pos hbeta hcrit

theorem triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control
    (beta J : Real) (z : Complex) (p q : Real) :
    ‖triangularIsingRaySymbolComplex J z p q -
        (triangularIsingSymbol beta beta (beta * J) p q : Complex)‖ <=
      triangularIsingComplexControl beta J z := by
  let A : Complex := (Real.cos p : Complex) + Real.cos q
  let B : Complex := (Real.cos (p + q) : Complex)
  have hA : ‖A‖ <= 2 := by
    calc
      ‖A‖ <= ‖(Real.cos p : Complex)‖ + ‖(Real.cos q : Complex)‖ :=
        norm_add_le _ _
      _ <= 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        nlinarith [Real.abs_cos_le_one p, Real.abs_cos_le_one q]
  have hB : ‖B‖ <= 1 := by
    change ‖(Real.cos (p + q) : Complex)‖ <= 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one (p + q)
  rw [← triangularIsingRaySymbolComplex_ofReal beta J p q]
  have heq : triangularIsingRaySymbolComplex J z p q -
      triangularIsingRaySymbolComplex J beta p q =
      (Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
        (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)) +
      (Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
        (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)) -
      (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)) * A -
      (Complex.sinh (2 * z * J) -
        (Real.sinh (2 * (beta * J)) : Complex)) * B := by
    have h2 : (2 : Complex) * beta = ((2 * beta : Real) : Complex) := by
      norm_num
    have hJ' : ((2 * beta : Real) : Complex) * J =
        ((2 * (beta * J) : Real) : Complex) := by
      norm_num
      ring
    unfold triangularIsingRaySymbolComplex A B
    rw [h2, hJ', ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    ring
  rw [heq]
  calc
    _ <=
        ‖Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
          (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)‖ +
        ‖Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
          (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)‖ +
        ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)‖ * ‖A‖ +
        ‖Complex.sinh (2 * z * J) -
          (Real.sinh (2 * (beta * J)) : Complex)‖ * ‖B‖ := by
      let X := Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
        (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)
      let Y := Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
        (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)
      let U := (Complex.sinh (2 * z) -
        (Real.sinh (2 * beta) : Complex)) * A
      let V := (Complex.sinh (2 * z * J) -
        (Real.sinh (2 * (beta * J)) : Complex)) * B
      change ‖X + Y - U - V‖ <=
        ‖X‖ + ‖Y‖ + ‖Complex.sinh (2 * z) -
          (Real.sinh (2 * beta) : Complex)‖ * ‖A‖ +
        ‖Complex.sinh (2 * z * J) -
          (Real.sinh (2 * (beta * J)) : Complex)‖ * ‖B‖
      rw [← norm_mul, ← norm_mul]
      calc
        ‖X + Y - U - V‖ <= ‖X + Y - U‖ + ‖V‖ := norm_sub_le _ _
        _ <= (‖X + Y‖ + ‖U‖) + ‖V‖ := by
          nlinarith [norm_sub_le (X + Y) U]
        _ <= (‖X‖ + ‖Y‖ + ‖U‖) + ‖V‖ := by
          nlinarith [norm_add_le X Y]
    _ <= triangularIsingComplexControl beta J z := by
      have hn1 := norm_nonneg (Complex.sinh (2 * z) -
        (Real.sinh (2 * beta) : Complex))
      have hn2 := norm_nonneg (Complex.sinh (2 * z * J) -
        (Real.sinh (2 * (beta * J)) : Complex))
      unfold triangularIsingComplexControl
      nlinarith [mul_le_mul_of_nonneg_left hA hn1,
        mul_le_mul_of_nonneg_left hB hn2,
        norm_nonneg (Complex.cosh (2 * z) - (Real.cosh (2 * beta) : Complex)),
        norm_nonneg (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)),
        norm_nonneg (Complex.cosh (2 * z * J) -
          (Real.cosh (2 * (beta * J)) : Complex)),
        norm_nonneg (Complex.sinh (2 * z * J) -
          (Real.sinh (2 * (beta * J)) : Complex))]

theorem triangularIsingComplexRadius_le_gap_half (beta J : Real) :
    triangularIsingComplexRadius beta J <= triangularIsingRayGap beta J / 2 :=
  min_le_left _ _

theorem triangularIsingComplexRadius_le_one (beta J : Real) :
    triangularIsingComplexRadius beta J <= 1 := min_le_right _ _


theorem triangularIsingComplex_factor_bounds
    {beta J : Real} {z : Complex}
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    ‖Complex.cosh (2 * z)‖ < |Real.cosh (2 * beta)| + 1 ∧
    ‖Complex.sinh (2 * z)‖ < |Real.sinh (2 * beta)| + 1 ∧
    ‖Complex.cosh (2 * z * J)‖ < |Real.cosh (2 * (beta * J))| + 1 ∧
    ‖Complex.sinh (2 * z * J)‖ < |Real.sinh (2 * (beta * J))| + 1 := by
  let dP := ‖Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
    (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)‖
  let dQ := ‖Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
    (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)‖
  let dC := ‖Complex.cosh (2 * z) - (Real.cosh (2 * beta) : Complex)‖
  let dS := ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)‖
  let dCJ := ‖Complex.cosh (2 * z * J) -
    (Real.cosh (2 * (beta * J)) : Complex)‖
  let dSJ := ‖Complex.sinh (2 * z * J) -
    (Real.sinh (2 * (beta * J)) : Complex)‖
  have hsum : dP + dQ + 2 * dS + dSJ + dC + dS + dCJ + dSJ < 1 := by
    have hcontrol : triangularIsingComplexControl beta J z < 1 :=
      hz.trans_le (triangularIsingComplexRadius_le_one beta J)
    simpa [triangularIsingComplexControl, dP, dQ, dC, dS, dCJ, dSJ]
      using hcontrol
  have hdP0 : 0 <= dP := by dsimp [dP]; positivity
  have hdQ0 : 0 <= dQ := by dsimp [dQ]; positivity
  have hdC0 : 0 <= dC := by dsimp [dC]; positivity
  have hdS0 : 0 <= dS := by dsimp [dS]; positivity
  have hdCJ0 : 0 <= dCJ := by dsimp [dCJ]; positivity
  have hdSJ0 : 0 <= dSJ := by dsimp [dSJ]; positivity
  have hdC : dC < 1 := by
    nlinarith
  have hdS : dS < 1 := by
    nlinarith
  have hdCJ : dCJ < 1 := by
    nlinarith
  have hdSJ : dSJ < 1 := by
    nlinarith
  have bound_of_sub {w : Complex} {r : Real}
      (h : ‖w - (r : Complex)‖ < 1) : ‖w‖ < |r| + 1 := by
    calc
      ‖w‖ = ‖(w - (r : Complex)) + (r : Complex)‖ := by ring_nf
      _ <= ‖w - (r : Complex)‖ + ‖(r : Complex)‖ := norm_add_le _ _
      _ < |r| + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith
  exact ⟨bound_of_sub hdC, bound_of_sub hdS,
    bound_of_sub hdCJ, bound_of_sub hdSJ⟩

theorem triangularIsingRaySymbolComplex_re_pos
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    0 < (triangularIsingRaySymbolComplex J z p q).re := by
  let m := triangularIsingRayGap beta J
  let d := triangularIsingRaySymbolComplex J z p q -
    (triangularIsingSymbol beta beta (beta * J) p q : Complex)
  have hm : 0 < m := triangularIsingRayGap_pos hbeta hcrit
  have hd : ‖d‖ < m / 2 :=
    (triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control beta J z p q).trans_lt
      (hz.trans_le (triangularIsingComplexRadius_le_gap_half beta J))
  have hdre : -‖d‖ <= d.re := neg_le_of_abs_le (Complex.abs_re_le_norm d)
  have hbase := triangularIsingRayGap_le_symbol (J := J) hbeta p q
  have hre : (triangularIsingRaySymbolComplex J z p q).re =
      triangularIsingSymbol beta beta (beta * J) p q + d.re := by
    dsimp [d]
    ring_nf
  rw [hre]
  dsimp [m] at hm hd hbase ⊢
  nlinarith

theorem triangularIsingRaySymbolComplex_mem_slitPlane
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    triangularIsingRaySymbolComplex J z p q ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (triangularIsingRaySymbolComplex_re_pos
    hbeta hcrit hz p q)

theorem triangularIsingRaySymbolComplex_norm_lower
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    triangularIsingRayGap beta J / 2 <
      ‖triangularIsingRaySymbolComplex J z p q‖ := by
  have hre := triangularIsingRaySymbolComplex_re_pos
    hbeta hcrit hz p q
  have hbase := triangularIsingRayGap_le_symbol (J := J) hbeta p q
  let d := triangularIsingRaySymbolComplex J z p q -
    (triangularIsingSymbol beta beta (beta * J) p q : Complex)
  have hd : ‖d‖ < triangularIsingRayGap beta J / 2 :=
    (triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control beta J z p q).trans_lt
      (hz.trans_le (triangularIsingComplexRadius_le_gap_half beta J))
  have hdre : -‖d‖ <= d.re := neg_le_of_abs_le (Complex.abs_re_le_norm d)
  have hreEq : (triangularIsingRaySymbolComplex J z p q).re =
      triangularIsingSymbol beta beta (beta * J) p q + d.re := by
    dsimp [d]
    ring_nf
  have hrenorm := Complex.re_le_norm (triangularIsingRaySymbolComplex J z p q)
  rw [hreEq] at hrenorm
  nlinarith

end
end StatMech.FrontierA
