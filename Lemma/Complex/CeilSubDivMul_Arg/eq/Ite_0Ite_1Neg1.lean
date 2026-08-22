import sympy.core.numbers
import sympy.core.power
import sympy.polys.polyroots
import Lemma.Complex.MulPowS_Inv3.eq.MulPow_Inv3Ite_1
import Lemma.Complex.ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0
import Lemma.Algebra.EqArg.of.Gt_0
import Lemma.Complex.ArgExpMulI.eq.Sub_Mul_Ceil
import Lemma.Algebra.Gt_Arg.Is.Eq_Ceil
import Lemma.Algebra.Or_Eq.Arg.of.Ceil.ne.Zero
import Lemma.Complex.Arg.in.IocNegPiPi
import Lemma.Set.Add.in.Ioc.of.In.In
import Lemma.Complex.EqSquareSqrt
open Algebra Complex Set


private lemma arg_cbrt
  {z : ℂ}
  (hz : z ≠ 0) :
    arg (z ^ (3 : ℂ)⁻¹) = arg z / 3 := by
  rw [cpow_def_of_ne_zero hz]
  have hlog :
      log z * (3 : ℂ)⁻¹ =
        ↑(Real.log ‖z‖ / 3) + ↑(arg z / 3) * I := by
    simp [log, div_eq_mul_inv]
    ring
  rw [hlog, exp_add, ← ofReal_exp]
  have hpos : Real.exp (Real.log ‖z‖ / 3) > 0 := Real.exp_pos _
  rw [EqArg.of.Gt_0 hpos]
  have hcast : ↑(arg z / 3) * I = I * (arg z / 3 : ℝ) := by
    simp
    ring
  rw [hcast, ArgExpMulI.eq.Sub_Mul_Ceil]
  have hceil : ⌈(arg z / 3) / (2 * π) - 1 / 2⌉ = 0 := by
    have harg := Arg.in.IocNegPiPi z
    have hπ : (0 : ℝ) < π := Real.pi_pos
    have hden : (0 : ℝ) < 6 * π := mul_pos (by norm_num) hπ
    have ha :
        (arg z / 3) / (2 * π) - 1 / 2 = arg z / (6 * π) - 1 / 2 := by
      field_simp
      ring
    rw [ha]
    apply Int.ceil_eq_iff.mpr
    constructor
    ·
      have hlt : -3 * π < arg z := by linarith [harg.1]
      have := div_lt_div_of_pos_right hlt hden
      have hsimp : (-3 * π) / (6 * π) = (-1 / 2 : ℝ) := by
        field_simp
        ring
      rw [hsimp] at this
      linarith
    ·
      have hle : arg z ≤ 3 * π := by linarith [harg.2]
      have : arg z / (6 * π) ≤ 1 / 2 :=
        (div_le_iff₀ hden).mpr (by linarith)
      linarith
  rw [hceil]
  ring


private lemma eq_exp_omega :
    exp (2 * π * I / 3) = -(1 / 2) + I * ↑(Real.sqrt 3) / 2 := by
  have hmul : (2 * π * I / 3 : ℂ) = ↑(2 * π / 3 : ℝ) * I := by
    simp [div_eq_mul_inv]
    ring
  rw [hmul, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hθ : (2 * π / 3 : ℝ) = π - π / 3 := by ring
  rw [hθ, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp
  ring


private lemma eq_exp_omega_conj :
    exp (-2 * π * I / 3) = -(1 / 2) - I * ↑(Real.sqrt 3) / 2 := by
  have hmul : (-2 * π * I / 3 : ℂ) = ↑(-2 * π / 3 : ℝ) * I := by
    simp [div_eq_mul_inv]
    ring
  rw [hmul, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hθ : (-2 * π / 3 : ℝ) = -(π - π / 3) := by ring
  rw [hθ, Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp
  ring


private lemma arg_omega :
    arg (-(1 / 2) + I * ↑(Real.sqrt 3) / 2) = 2 * π / 3 := by
  rw [← eq_exp_omega]
  have hmul : (2 * π * I / 3 : ℂ) = I * (2 * π / 3 : ℝ) := by
    simp [div_eq_mul_inv]
    ring
  rw [hmul, ArgExpMulI.eq.Sub_Mul_Ceil]
  have hceil : ⌈(2 * π / 3) / (2 * π) - 1 / 2⌉ = 0 := by
    have ha : (2 * π / 3) / (2 * π) - 1 / 2 = (-1 / 6 : ℝ) := by
      field_simp
      ring
    rw [ha]
    apply Int.ceil_eq_iff.mpr
    constructor <;> norm_num
  rw [hceil]
  ring


private lemma arg_omega_conj :
    arg (-(1 / 2) - I * ↑(Real.sqrt 3) / 2) = -2 * π / 3 := by
  rw [← eq_exp_omega_conj]
  have hmul : (-2 * π * I / 3 : ℂ) = I * (-2 * π / 3 : ℝ) := by
    simp [div_eq_mul_inv]
    ring
  rw [hmul, ArgExpMulI.eq.Sub_Mul_Ceil]
  have hceil : ⌈(-2 * π / 3) / (2 * π) - 1 / 2⌉ = 0 := by
    have ha : (-2 * π / 3) / (2 * π) - 1 / 2 = (-5 / 6 : ℝ) := by
      field_simp
      ring
    rw [ha]
    apply Int.ceil_eq_iff.mpr
    constructor <;> norm_num
  rw [hceil]
  ring


@[main]
private lemma main
  {p q : ℂ} :
-- imply
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let U : ℂ := √δ - q
  let V : ℂ := -√δ - q
  ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉ =
    if ⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ = 0 then
      (0 : ℤ)
    else if arg U + arg V > π then
      1
    else
      -1 := by
-- proof
  intro δ U V
  classical
  have hsq : √δ * √δ = δ := by
    simpa [pow_two] using (EqSquareSqrt : (√δ)² = δ)
  have hUV : U * V = -(4 * p ^ 3 / 27) := by
    simp only [U, V]
    rw [show (√δ - q) * (-√δ - q) = q ^ 2 - √δ * √δ by ring, hsq]
    simp only [δ]
    ring
  by_cases hp : p = 0
  ·
    have hexp : (3 : ℂ)⁻¹ ≠ 0 := by norm_num
    have hz : (0 : ℂ) ^ (3 : ℂ)⁻¹ = 0 := zero_cpow hexp
    have hUV0 : U * V = 0 := by
      simp [hUV, hp]
    have hprod : U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹ = 0 := by
      rcases mul_eq_zero.mp hUV0 with hU | hV
      ·
        simp [hU, hz]
      ·
        simp [hV, hz]
    have harg : arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) = 0 := by
      rw [hprod, arg_zero]
    have hceil0 : ⌈(-1 / 2 : ℝ)⌉ = 0 := by
      apply Int.ceil_eq_iff.mpr
      constructor <;> norm_num
    have hsimp :
        3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2 = -1 / 2 := by
      rw [harg]
      ring
    rw [hsimp, hceil0]
    have hθ₁ : -π < arg U + arg V := by
      rcases mul_eq_zero.mp hUV0 with hU0 | hV0
      ·
        simpa [hU0, arg_zero] using (Arg.in.IocNegPiPi V).1
      ·
        simpa [hV0, arg_zero] using (Arg.in.IocNegPiPi U).1
    have hθ₂ : arg U + arg V ≤ π := by
      rcases mul_eq_zero.mp hUV0 with hU0 | hV0
      ·
        simpa [hU0, arg_zero] using (Arg.in.IocNegPiPi V).2
      ·
        simpa [hV0, arg_zero] using (Arg.in.IocNegPiPi U).2
    have hcond : ⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ = 0 := by
      have hπ : (0 : ℝ) < π := Real.pi_pos
      have hden : (0 : ℝ) < 2 * π := mul_pos (by norm_num) hπ
      apply Int.ceil_eq_iff.mpr
      constructor
      ·
        have := div_lt_div_of_pos_right hθ₁ hden
        have hsimp' : (-π) / (2 * π) = (-1 / 2 : ℝ) := by
          field_simp
        rw [hsimp'] at this
        linarith
      ·
        have : (arg U + arg V) / (2 * π) ≤ 1 / 2 :=
          (div_le_iff₀ hden).mpr (by linarith [hθ₂])
        linarith
    rw [if_pos hcond]
  ·
    have hUV0 : U * V ≠ 0 := by
      rw [hUV]
      refine neg_ne_zero.mpr (div_ne_zero ?_ (by norm_num))
      exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hp)
    have hU : U ≠ 0 := left_ne_zero_of_mul hUV0
    have hV : V ≠ 0 := right_ne_zero_of_mul hUV0
    let d : ℤ := ⌈(arg U + arg V) / (2 * π) - 1 / 2⌉
    have hUV_cbrt : (U * V) ^ (3 : ℂ)⁻¹ ≠ 0 := by
      rw [cpow_def_of_ne_zero hUV0]
      exact exp_ne_zero _
    have hfac :
        (if U = 0 ∨ V = 0 ∨ d = 0 then (1 : ℂ)
          else if arg U + arg V > π then
            -(1 / 2) + I * ↑(Real.sqrt 3) / 2
          else
            -(1 / 2) - I * ↑(Real.sqrt 3) / 2) ≠ 0 := by
      split_ifs
      ·
        exact one_ne_zero
      ·
        rw [← eq_exp_omega]
        exact exp_ne_zero _
      ·
        rw [← eq_exp_omega_conj]
        exact exp_ne_zero _
    have harg_fac :
        arg
            (if U = 0 ∨ V = 0 ∨ d = 0 then (1 : ℂ)
              else if arg U + arg V > π then
                -(1 / 2) + I * ↑(Real.sqrt 3) / 2
              else
                -(1 / 2) - I * ↑(Real.sqrt 3) / 2) =
          2 * π * d / 3 := by
      split_ifs with h0 hgt
      ·
        have hd0 : d = 0 := by
          rcases h0 with hU0 | h0
          ·
            exact (hU hU0).elim
          ·
            rcases h0 with hV0 | hd0
            ·
              exact (hV hV0).elim
            ·
              exact hd0
        simp [arg_one, hd0]
      ·
        have hd1 : d = 1 := (Gt_Arg.Is.Eq_Ceil (A := U) (B := V)).mp hgt
        rw [hd1, arg_omega]
        ring
      ·
        have ⟨_, hrest⟩ := not_or.mp h0
        have ⟨_, hdne⟩ := not_or.mp hrest
        have hor := Or_Eq.Arg.of.Ceil.ne.Zero hdne
        have hdne1 : d ≠ 1 := by
          intro hd1
          exact hgt ((Gt_Arg.Is.Eq_Ceil (A := U) (B := V)).mpr hd1)
        have hdneg : d = -1 := by
          rcases hor with h | h
          ·
            contradiction
          ·
            exact h
        rw [hdneg, arg_omega_conj]
        ring
    have harg_prod :
        arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) = (arg U + arg V) / 3 := by
      rw [MulPowS_Inv3.eq.MulPow_Inv3Ite_1 (A := U) (B := V)]
      rw [ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0 hUV_cbrt hfac, arg_cbrt hUV0, harg_fac]
      have hargUV := ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0 hU hV
      have hsum :
          arg (U * V) / 3 + 2 * π * d / 3 = (arg U + arg V) / 3 := by
        rw [hargUV]
        simp [d]
        ring
      have hwrap : ⌈((arg U + arg V) / 3) / (2 * π) - 1 / 2⌉ = 0 := by
        have hUarg := Arg.in.IocNegPiPi U
        have hVarg := Arg.in.IocNegPiPi V
        have hsumI := Add.in.Ioc.of.In.In hUarg hVarg
        have hπ : (0 : ℝ) < π := Real.pi_pos
        have hden : (0 : ℝ) < 6 * π := mul_pos (by norm_num) hπ
        have ha :
            ((arg U + arg V) / 3) / (2 * π) - 1 / 2 =
              (arg U + arg V) / (6 * π) - 1 / 2 := by
          field_simp
          ring
        rw [ha]
        apply Int.ceil_eq_iff.mpr
        constructor
        ·
          have hlt : -3 * π < arg U + arg V := by linarith [hsumI.1]
          have := div_lt_div_of_pos_right hlt hden
          have hsimp : (-3 * π) / (6 * π) = (-1 / 2 : ℝ) := by
            field_simp
            ring
          rw [hsimp] at this
          linarith
        ·
          have hle : arg U + arg V ≤ 3 * π := by linarith [hsumI.2]
          have : (arg U + arg V) / (6 * π) ≤ 1 / 2 :=
            (div_le_iff₀ hden).mpr (by linarith)
          linarith
      simp only [hsum, hwrap, mul_zero, sub_zero, Int.cast_zero]
    rw [harg_prod]
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have hsimp :
        3 * ((arg U + arg V) / 3) / (2 * π) - 1 / 2 =
          (arg U + arg V) / (2 * π) - 1 / 2 := by
      field_simp [h3]
    rw [hsimp]
    split_ifs with hd0 hgt
    ·
      exact hd0
    ·
      have hd1 : d = 1 := (Gt_Arg.Is.Eq_Ceil (A := U) (B := V)).mp hgt
      exact hd1
    ·
      have hdne : d ≠ 0 := by
        intro hd
        exact hd0 hd
      have hor := Or_Eq.Arg.of.Ceil.ne.Zero hdne
      have hdne1 : d ≠ 1 := by
        intro hd1
        exact hgt ((Gt_Arg.Is.Eq_Ceil (A := U) (B := V)).mpr hd1)
      rcases hor with h | h
      ·
        contradiction
      ·
        exact h


-- created on 2018-11-08
-- updated on 2026-08-22
