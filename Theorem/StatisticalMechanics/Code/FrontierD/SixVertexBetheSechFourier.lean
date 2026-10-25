/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part4
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
open Filter MeasureTheory Set Topology
open scoped FourierTransform


namespace StatMech.FrontierD

noncomputable section

theorem image_logistic_Ioo :
    (fun t : Real => t / (1 - t)) '' Set.Ioo 0 1 = Set.Ioi 0 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact div_pos ht.1 (sub_pos.mpr ht.2)
  · intro hy
    let t := y / (1 + y)
    have hy' : 0 < y := hy
    have hden : 0 < 1 + y := by linarith
    have ht : t ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · exact div_pos hy hden
      · rw [div_lt_one hden]
        linarith
    refine ⟨t, ht, ?_⟩
    dsimp [t]
    field_simp [hden.ne']
    ring

theorem hasDerivWithinAt_logistic
    (t : Real) (ht : t ∈ Set.Ioo 0 1) :
    HasDerivWithinAt (fun s : Real => s / (1 - s))
      (1 / (1 - t) ^ 2) (Set.Ioo 0 1) t := by
  have hne : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
  convert ((hasDerivAt_id t).div
    ((hasDerivAt_id t).const_sub 1) hne).hasDerivWithinAt using 1
  simp only [id_eq]
  field_simp [hne]
  ring

theorem injOn_logistic :
    Set.InjOn (fun t : Real => t / (1 - t)) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have hxden : 0 < 1 - x := sub_pos.mpr hx.2
  have hyden : 0 < 1 - y := sub_pos.mpr hy.2
  rw [div_eq_div_iff hxden.ne' hyden.ne'] at hxy
  linarith

theorem integral_Ioi_cpow_div_one_add
    (u : Complex) :
    (∫ y : Real in Set.Ioi 0,
      (y : Complex) ^ (u - 1) / (1 + y)) =
      Complex.betaIntegral u (1 - u) := by
  let f : Real → Real := fun t => t / (1 - t)
  let f' : Real → Real := fun t => 1 / (1 - t) ^ 2
  let g : Real → Complex := fun y =>
    (y : Complex) ^ (u - 1) / (1 + y)
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (0 : Real) 1) measurableSet_Ioo
    (fun t ht => hasDerivWithinAt_logistic t ht)
    injOn_logistic g
  rw [image_logistic_Ioo] at hchange
  rw [hchange]
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num)]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hft : 0 < f t := div_pos ht0 ht1
  have hf' : 0 < f' t := by
    dsimp [f']
    positivity
  dsimp [f, f', g] at hf' ⊢
  rw [abs_of_pos hf']
  rw [show t / (1 - t) = t * (1 / (1 - t)) by ring]
  rw [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg ht0.le
    (one_div_nonneg.mpr ht1.le)]
  push_cast
  have hbase : (1 : Complex) - t = ((1 - t : Real) : Complex) := by
    norm_num
  have hbaseNe : (1 : Complex) - t ≠ 0 := by
    rw [hbase]
    exact Complex.ofReal_ne_zero.mpr ht1.ne'
  have harg : ((1 - (t : Complex))).arg ≠ Real.pi := by
    rw [hbase]
    rw [Complex.arg_ofReal_of_nonneg ht1.le]
    exact Real.pi_ne_zero.symm
  simp only [one_div]
  rw [Complex.inv_cpow (1 - t) (u - 1) harg]
  rw [← Complex.cpow_neg]
  rw [show (1 : Complex) + (t : Complex) *
        ((1 : Complex) - t)⁻¹ = ((1 : Complex) - t)⁻¹ by
    field_simp [hbaseNe]
    ring]
  rw [div_inv_eq_mul]
  rw [show (1 - u : Complex) - 1 = -u by ring]
  let B : Complex := 1 - t
  have hBne : B ≠ 0 := hbaseNe
  have hInvSq : (B ^ 2)⁻¹ = B ^ (-(2 : Complex)) := by
    calc
      (B ^ 2)⁻¹ = (B ^ (2 : Complex))⁻¹ := by
        exact congrArg Inv.inv (Complex.cpow_natCast B 2).symm
      _ = B ^ (-(2 : Complex)) := (Complex.cpow_neg B 2).symm
  have hpow : (B ^ 2)⁻¹ * (B ^ (-(u - 1)) * B) = B ^ (-u) := by
    rw [hInvSq]
    conv_lhs =>
      rhs
      rhs
      rw [show B = B ^ (1 : Complex) by rw [Complex.cpow_one]]
    rw [← Complex.cpow_add _ _ hBne, ← Complex.cpow_add _ _ hBne]
    congr 1
    ring
  have hpow' : (((1 : Complex) - t) ^ 2)⁻¹ *
      (((1 : Complex) - t) ^ (-(u - 1)) * ((1 : Complex) - t)) =
      ((1 : Complex) - t) ^ (-u) := by
    simpa only [B] using hpow
  rw [show (((1 : Complex) - t) ^ 2)⁻¹ *
      ((t : Complex) ^ (u - 1) *
        ((1 : Complex) - t) ^ (-(u - 1)) * ((1 : Complex) - t)) =
    (t : Complex) ^ (u - 1) *
      ((((1 : Complex) - t) ^ 2)⁻¹ *
        (((1 : Complex) - t) ^ (-(u - 1)) * ((1 : Complex) - t))) by
      ring,
    hpow']

theorem image_exp_univ :
    Real.exp '' Set.univ = Set.Ioi 0 := by
  rw [Set.image_univ, Real.range_exp]

theorem integral_cexp_mul_div_one_add_rexp
    (u : Complex) :
    (∫ x : Real, Complex.exp (u * x) / (1 + Real.exp x)) =
      Complex.betaIntegral u (1 - u) := by
  let g : Real → Complex := fun y =>
    (y : Complex) ^ (u - 1) / (1 + y)
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_exp_univ] at hchange
  rw [← integral_Ioi_cpow_div_one_add u, hchange]
  simp only [Measure.restrict_univ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  dsimp [g]
  rw [abs_of_pos (Real.exp_pos x)]
  symm
  change (Real.exp x : Complex) *
      ((Real.exp x : Complex) ^ (u - 1) /
        (1 + (Real.exp x : Complex))) =
    Complex.exp (u * x) / (1 + (Real.exp x : Complex))
  have hexp : Complex.exp (x : Complex) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.ofReal_exp]
  conv_lhs =>
    lhs
    rw [show Complex.exp (x : Complex) =
      Complex.exp (x : Complex) ^ (1 : Complex) by
        rw [Complex.cpow_one]]
  rw [show Complex.exp (x : Complex) ^ (1 : Complex) *
      (Complex.exp (x : Complex) ^ (u - 1) /
        (1 + Complex.exp (x : Complex))) =
      (Complex.exp (x : Complex) ^ (1 : Complex) *
        Complex.exp (x : Complex) ^ (u - 1)) /
          (1 + Complex.exp (x : Complex)) by ring]
  rw [← Complex.cpow_add _ _ hexp]
  rw [Complex.cpow_def_of_ne_zero hexp]
  rw [Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  congr 1
  ring_nf

theorem betaIntegral_one_sub_eq_pi_div_sin
    {u : Complex} (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    Complex.betaIntegral u (1 - u) =
      Real.pi / Complex.sin (Real.pi * u) := by
  have hv : 0 < (1 - u).re := by
    change 0 < 1 - u.re
    linarith
  have hGamma := Complex.Gamma_mul_Gamma_eq_betaIntegral hu0 hv
  calc
    Complex.betaIntegral u (1 - u) =
        Complex.Gamma 1 * Complex.betaIntegral u (1 - u) := by
          rw [Complex.Gamma_one, one_mul]
    _ = Complex.Gamma u * Complex.Gamma (1 - u) := by
      rw [show u + (1 - u) = (1 : Complex) by ring] at hGamma
      exact hGamma.symm
    _ = Real.pi / Complex.sin (Real.pi * u) :=
      Complex.Gamma_mul_Gamma_one_sub u

theorem betaIntegral_half_sub_mul_I
    (t : Real) :
    Complex.betaIntegral
        ((1 : Complex) / 2 - (t / Real.pi) * Complex.I)
        (1 - ((1 : Complex) / 2 - (t / Real.pi) * Complex.I)) =
      Real.pi / Real.cosh t := by
  let u : Complex := (1 : Complex) / 2 - (t / Real.pi) * Complex.I
  have hu0 : 0 < u.re := by simp [u]
  have hu1 : u.re < 1 := by norm_num [u]
  rw [betaIntegral_one_sub_eq_pi_div_sin hu0 hu1]
  have harg : (Real.pi : Complex) * u =
      (Real.pi : Complex) / 2 - (t : Complex) * Complex.I := by
    dsimp [u]
    field_simp [Real.pi_ne_zero]
  rw [harg, Complex.sin_pi_div_two_sub, Complex.cos_mul_I]
  rw [← Complex.ofReal_cosh]

theorem one_div_cosh_eq_two_mul_exp_div
    (x : Real) :
    1 / Real.cosh x =
      2 * Real.exp x / (1 + Real.exp (2 * x)) := by
  rw [Real.cosh_eq]
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero _
  have hneg : Real.exp (-x) = (Real.exp x)⁻¹ := by
    rw [← Real.exp_neg]
  have htwo : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [hneg, htwo]
  field_simp [hexp]
  ring

theorem integral_fourier_sech
    {lam : Real} (hlam : 0 < lam) (n : Real) :
    (∫ x : Real,
      Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) /
        Real.cosh (Real.pi ^ 2 * x / lam)) =
      (lam / Real.pi : Real) / Real.cosh (n * lam) := by
  let A : Real := Real.pi ^ 2 / lam
  let b : Real := 2 * A
  let u : Complex :=
    (1 : Complex) / 2 - ((n * lam) / Real.pi) * Complex.I
  let g : Real → Complex := fun t =>
    Complex.exp (u * t) / (1 + Real.exp t)
  have hA : 0 < A := div_pos (sq_pos_of_pos Real.pi_pos) hlam
  have hb : 0 < b := mul_pos (by norm_num) hA
  have hpoint (x : Real) :
      Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) /
          Real.cosh (Real.pi ^ 2 * x / lam) =
        2 * g (b * x) := by
    have hscale : Real.pi ^ 2 * x / lam = A * x := by
      dsimp [A]
      field_simp [hlam.ne']
    rw [hscale, div_eq_mul_inv]
    have hsechC : ((Real.cosh (A * x) : Real) : Complex)⁻¹ =
        ((2 * Real.exp (A * x) /
          (1 + Real.exp (2 * (A * x))) : Real) : Complex) := by
      rw [← Complex.ofReal_inv]
      exact congrArg (fun r : Real => (r : Complex))
        (by simpa [one_div] using
          one_div_cosh_eq_two_mul_exp_div (A * x))
    rw [hsechC]
    dsimp [g]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    have hden : Complex.exp (2 * ((A : Complex) * x)) =
        Complex.exp ((b : Complex) * x) := by
      congr 1
      dsimp [b]
      push_cast
      ring
    rw [hden]
    rw [show Complex.exp (-2 * (Real.pi : Complex) *
          ((x : Complex) * n) * Complex.I) *
          (2 * Complex.exp ((A : Complex) * x) *
            (1 + Complex.exp ((b : Complex) * x))⁻¹) =
        2 * (Complex.exp (-2 * (Real.pi : Complex) *
          ((x : Complex) * n) * Complex.I) *
            Complex.exp ((A : Complex) * x)) *
              (1 + Complex.exp ((b : Complex) * x))⁻¹ by ring]
    rw [← Complex.exp_add]
    have hexponent :
        -2 * (Real.pi : Complex) * ((x : Complex) * n) * Complex.I +
            (A : Complex) * x =
          u * ((b : Complex) * x) := by
      dsimp [u, b, A]
      push_cast
      field_simp [hlam.ne', Real.pi_ne_zero]
      ring
    rw [hexponent]
    ring
  rw [show (fun x : Real =>
      Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) /
        Real.cosh (Real.pi ^ 2 * x / lam)) =
      fun x => 2 * g (b * x) by
        funext x
        exact hpoint x]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_mul_left g b]
  rw [abs_of_pos (inv_pos.mpr hb)]
  rw [integral_cexp_mul_div_one_add_rexp u]
  have hbeta : Complex.betaIntegral u (1 - u) =
      Real.pi / Real.cosh (n * lam) := by
    convert betaIntegral_half_sub_mul_I (n * lam) using 1 <;>
      dsimp [u] <;> push_cast <;> ring
  rw [hbeta]
  rw [Complex.real_smul]
  dsimp [b, A]
  push_cast
  field_simp [hlam.ne', Real.pi_ne_zero]


end
end StatMech.FrontierD
