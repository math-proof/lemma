/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part4
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

theorem norm_add_four_sub_two_le
    (a b c d e f : Complex) :
    ‖a + b + c + d - e - f‖ <=
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  calc
    ‖a + b + c + d - e - f‖ <= ‖a + b + c + d - e‖ + ‖f‖ := norm_sub_le _ _
    _ <= (‖a + b + c + d‖ + ‖e‖) + ‖f‖ := by
      nlinarith [norm_sub_le (a + b + c + d) e]
    _ <= ((‖a + b + c‖ + ‖d‖) + ‖e‖) + ‖f‖ := by
      nlinarith [norm_add_le (a + b + c) d]
    _ <= (((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖ := by
      nlinarith [norm_add_le (a + b) c]
    _ <= ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
      nlinarith [norm_add_le a b]

theorem triangularIsingLogRaySymbolComplexDeriv_norm_le
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    ‖triangularIsingLogRaySymbolComplexDeriv J z p q‖ <=
      triangularIsingComplexDerivBound beta J /
        (triangularIsingRayGap beta J / 2) := by
  obtain ⟨hC, hS, hCJ, hSJ⟩ := triangularIsingComplex_factor_bounds hz
  have hA : ‖(Real.cos p : Complex) + Real.cos q‖ <= 2 := by
    calc
      _ <= ‖(Real.cos p : Complex)‖ + ‖(Real.cos q : Complex)‖ := norm_add_le _ _
      _ <= 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        nlinarith [Real.abs_cos_le_one p, Real.abs_cos_le_one q]
  have hB : ‖(Real.cos (p + q) : Complex)‖ <= 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  let C0 := |Real.cosh (2 * beta)| + 1
  let S0 := |Real.sinh (2 * beta)| + 1
  let CJ0 := |Real.cosh (2 * (beta * J))| + 1
  let SJ0 := |Real.sinh (2 * (beta * J))| + 1
  let t1 : Complex := 4 * Complex.cosh (2 * z) * Complex.sinh (2 * z) *
    Complex.cosh (2 * z * J)
  let t2 : Complex := 2 * J * Complex.cosh (2 * z) ^ 2 *
    Complex.sinh (2 * z * J)
  let t3 : Complex := 4 * Complex.sinh (2 * z) * Complex.cosh (2 * z) *
    Complex.sinh (2 * z * J)
  let t4 : Complex := 2 * J * Complex.sinh (2 * z) ^ 2 *
    Complex.cosh (2 * z * J)
  let t5 : Complex := 2 * Complex.cosh (2 * z) *
    ((Real.cos p : Complex) + Real.cos q)
  let t6 : Complex := 2 * J * Complex.cosh (2 * z * J) *
    (Real.cos (p + q) : Complex)
  have ht1 : ‖t1‖ <= 4 * C0 * S0 * CJ0 := by
    dsimp [t1, C0, S0, CJ0]
    simp only [norm_mul, norm_ofNat]
    gcongr
  have ht2 : ‖t2‖ <= 2 * |J| * C0 ^ 2 * SJ0 := by
    dsimp [t2, C0, SJ0]
    simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      norm_pow]
    gcongr
  have ht3 : ‖t3‖ <= 4 * S0 * C0 * SJ0 := by
    dsimp [t3, S0, C0, SJ0]
    simp only [norm_mul, norm_ofNat]
    gcongr
  have ht4 : ‖t4‖ <= 2 * |J| * S0 ^ 2 * CJ0 := by
    dsimp [t4, S0, CJ0]
    simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      norm_pow]
    gcongr
  have ht5 : ‖t5‖ <= 4 * C0 := by
    dsimp [t5, C0]
    simp only [norm_mul, norm_ofNat]
    have hnonneg : 0 <= ‖Complex.cosh (2 * z)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hA hnonneg,
      mul_le_mul_of_nonneg_left hC.le (by norm_num : (0 : Real) <= 4)]
  have ht6 : ‖t6‖ <= 2 * |J| * CJ0 := by
    dsimp [t6, CJ0]
    simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    have hJ0 : 0 <= |J| := abs_nonneg J
    have hCJ0 : 0 <= ‖Complex.cosh (2 * z * J)‖ := norm_nonneg _
    have hfac : 0 <= 2 * |J| * ‖Complex.cosh (2 * z * J)‖ := by positivity
    calc
      2 * |J| * ‖Complex.cosh (2 * z * J)‖ *
          |Real.cos (p + q)| <=
          2 * |J| * ‖Complex.cosh (2 * z * J)‖ := by
        nth_rewrite 2 [← mul_one (2 * |J| * ‖Complex.cosh (2 * z * J)‖)]
        exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hfac
      _ <= 2 * |J| * (|Real.cosh (2 * (beta * J))| + 1) := by
        exact mul_le_mul_of_nonneg_left hCJ.le (by positivity)
  have hnum : ‖triangularIsingRaySymbolComplexDeriv J z p q‖ <=
      triangularIsingComplexDerivBound beta J := by
    calc
      ‖triangularIsingRaySymbolComplexDeriv J z p q‖ =
          ‖t1 + t2 + t3 + t4 - t5 - t6‖ := by rfl
      _ <= ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ + ‖t5‖ + ‖t6‖ :=
        norm_add_four_sub_two_le t1 t2 t3 t4 t5 t6
      _ <= 4 * C0 * S0 * CJ0 + 2 * |J| * C0 ^ 2 * SJ0 +
          4 * S0 * C0 * SJ0 + 2 * |J| * S0 ^ 2 * CJ0 +
          4 * C0 + 2 * |J| * CJ0 := by nlinarith
      _ = triangularIsingComplexDerivBound beta J := by
        simp [triangularIsingComplexDerivBound, C0, S0, CJ0, SJ0]
  have hden := triangularIsingRaySymbolComplex_norm_lower
    hbeta hcrit hz p q
  have hgap := triangularIsingRayGap_pos hbeta hcrit
  have hbound0 : 0 <= triangularIsingComplexDerivBound beta J := by
    unfold triangularIsingComplexDerivBound
    positivity
  rw [triangularIsingLogRaySymbolComplexDeriv, norm_div]
  exact div_le_div₀ hbound0 hnum (by positivity) hden.le

theorem hasDerivAt_triangularIsingRaySymbolComplex
    (J : Real) (z : Complex) (p q : Real) :
    HasDerivAt (fun w => triangularIsingRaySymbolComplex J w p q)
      (triangularIsingRaySymbolComplexDeriv J z p q) z := by
  have hlin : HasDerivAt (fun w : Complex => 2 * w) 2 z := by
    convert (hasDerivAt_id z).const_mul 2 using 1 <;> ring
  have hlinJ : HasDerivAt (fun w : Complex => 2 * w * J) (2 * J) z := by
    convert ((hasDerivAt_id z).const_mul 2).mul_const J using 1 <;> ring
  have hC := (Complex.hasDerivAt_cosh (2 * z)).comp z hlin
  have hS := (Complex.hasDerivAt_sinh (2 * z)).comp z hlin
  have hCJ := (Complex.hasDerivAt_cosh (2 * z * J)).comp z hlinJ
  have hSJ := (Complex.hasDerivAt_sinh (2 * z * J)).comp z hlinJ
  have h := ((hC.pow 2).mul hCJ).add ((hS.pow 2).mul hSJ) |>.sub
    ((hS.mul_const ((Real.cos p : Complex) + Real.cos q)).add
      (hSJ.mul_const (Real.cos (p + q) : Complex)))
  convert h using 1
  unfold triangularIsingRaySymbolComplexDeriv
  simp only [Function.comp_apply, Pi.pow_apply, Nat.reduceSub, pow_one]
  ring

theorem hasDerivAt_log_triangularIsingRaySymbolComplex
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    HasDerivAt (fun w => Complex.log (triangularIsingRaySymbolComplex J w p q))
      (triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
  simpa [triangularIsingLogRaySymbolComplexDeriv] using
    (hasDerivAt_triangularIsingRaySymbolComplex J z p q).clog
      (triangularIsingRaySymbolComplex_mem_slitPlane hbeta hcrit hz p q)

theorem continuous_triangularIsingComplexLog_momenta
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    Continuous (fun x : Real × Real =>
      Complex.log (triangularIsingRaySymbolComplex J z x.1 x.2)) := by
  have hs : Continuous (fun x : Real × Real =>
      triangularIsingRaySymbolComplex J z x.1 x.2) := by
    unfold triangularIsingRaySymbolComplex
    fun_prop
  rw [continuous_iff_continuousAt]
  intro x
  have hlog : ContinuousAt Complex.log
      (triangularIsingRaySymbolComplex J z x.1 x.2) :=
    (Complex.hasDerivAt_log
      (triangularIsingRaySymbolComplex_mem_slitPlane
        hbeta hcrit hz x.1 x.2)).continuousAt
  exact ContinuousAt.comp'
    (f := fun y : Real × Real =>
      triangularIsingRaySymbolComplex J z y.1 y.2)
    hlog hs.continuousAt

theorem continuous_triangularIsingComplexLogDeriv_momenta
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    Continuous (fun x : Real × Real =>
      triangularIsingLogRaySymbolComplexDeriv J z x.1 x.2) := by
  unfold triangularIsingLogRaySymbolComplexDeriv
  apply Continuous.div
  · unfold triangularIsingRaySymbolComplexDeriv
    fun_prop
  · unfold triangularIsingRaySymbolComplex
    fun_prop
  · intro x hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re] at hre
    exact (triangularIsingRaySymbolComplex_re_pos
      hbeta hcrit hz x.1 x.2).ne' hre

theorem continuous_triangularIsingComplexInnerLog
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    Continuous (fun p => ∫ q in (-Real.pi)..Real.pi,
      Complex.log (triangularIsingRaySymbolComplex J z p q)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_triangularIsingComplexLog_momenta hbeta hcrit hz)
    (-Real.pi) Real.pi

theorem continuous_triangularIsingComplexInnerLogDeriv
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    Continuous (fun p => ∫ q in (-Real.pi)..Real.pi,
      triangularIsingLogRaySymbolComplexDeriv J z p q) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_triangularIsingComplexLogDeriv_momenta hbeta hcrit hz)
    (-Real.pi) Real.pi

theorem hasDerivAt_triangularIsingComplexInnerIntegral
    {beta J : Real} {z : Complex} (p : Real)
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    HasDerivAt (fun w => ∫ q in (-Real.pi)..Real.pi,
      Complex.log (triangularIsingRaySymbolComplex J w p q))
      (∫ q in (-Real.pi)..Real.pi,
        triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
  let C := triangularIsingComplexDerivBound beta J /
    (triangularIsingRayGap beta J / 2)
  have hs : triangularIsingComplexNeighborhood beta J ∈ nhds z :=
    (triangularIsingComplexNeighborhood_isOpen beta J).mem_nhds hz
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w q => Complex.log (triangularIsingRaySymbolComplex J w p q))
    (F' := fun w q => triangularIsingLogRaySymbolComplexDeriv J w p q)
    (bound := fun _ => C) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with w hw
    exact ((continuous_triangularIsingComplexLog_momenta
      hbeta hcrit hw).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ((continuous_triangularIsingComplexLog_momenta
      hbeta hcrit hz).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact ((continuous_triangularIsingComplexLogDeriv_momenta
      hbeta hcrit hz).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with q _hq w hw
    simpa only [C] using
      triangularIsingLogRaySymbolComplexDeriv_norm_le
        hbeta hcrit hw p q
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with q _hq w hw
    exact hasDerivAt_log_triangularIsingRaySymbolComplex
      hbeta hcrit hw p q

theorem hasDerivAt_triangularIsingComplexDoubleIntegral
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    HasDerivAt (fun w => ∫ p in (-Real.pi)..Real.pi,
      ∫ q in (-Real.pi)..Real.pi,
        Complex.log (triangularIsingRaySymbolComplex J w p q))
      (∫ p in (-Real.pi)..Real.pi,
        ∫ q in (-Real.pi)..Real.pi,
          triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
  let C := triangularIsingComplexDerivBound beta J /
    (triangularIsingRayGap beta J / 2)
  let B := C * (2 * Real.pi)
  have hs : triangularIsingComplexNeighborhood beta J ∈ nhds z :=
    (triangularIsingComplexNeighborhood_isOpen beta J).mem_nhds hz
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w p => ∫ q in (-Real.pi)..Real.pi,
      Complex.log (triangularIsingRaySymbolComplex J w p q))
    (F' := fun w p => ∫ q in (-Real.pi)..Real.pi,
      triangularIsingLogRaySymbolComplexDeriv J w p q)
    (bound := fun _ => B) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with w hw
    exact (continuous_triangularIsingComplexInnerLog
      hbeta hcrit hw).aestronglyMeasurable
  · exact (continuous_triangularIsingComplexInnerLog
      hbeta hcrit hz).intervalIntegrable _ _
  · exact (continuous_triangularIsingComplexInnerLogDeriv
      hbeta hcrit hz).aestronglyMeasurable
  · filter_upwards [] with p _hp w hw
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi)
      (f := fun q => triangularIsingLogRaySymbolComplexDeriv J w p q)
      (C := C) (fun q _hq => by
        simpa only [C] using
          triangularIsingLogRaySymbolComplexDeriv_norm_le
            hbeta hcrit hw p q)
    calc
      ‖∫ q in (-Real.pi)..Real.pi,
          triangularIsingLogRaySymbolComplexDeriv J w p q‖ <=
          C * |Real.pi - (-Real.pi)| := hbound
      _ = B := by
        rw [abs_of_pos (by linarith [Real.pi_pos])]
        simp only [B]
        ring
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with p _hp w hw
    exact hasDerivAt_triangularIsingComplexInnerIntegral
      p hbeta hcrit hw


end
end StatMech.FrontierA
