import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Set


private lemma setIntegral_Ioi_comp_one_add (h : ℝ → ℂ) :
  ∫ y in Ioi (0 : ℝ), h (1 + y) = ∫ t in Ioi (1 : ℝ), h t := by
  have hfun : (fun y => (Ioi (0 : ℝ)).indicator (fun y => h (1 + y)) y) =
    fun y => (Ioi (1 : ℝ)).indicator h (1 + y) := by
    funext y
    if hy : 0 < y then
      rw [Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy),
        Set.indicator_of_mem (show 1 + y ∈ Ioi (1 : ℝ) by rw [Set.mem_Ioi]; linarith)]
    else
      rw [Set.indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy),
        Set.indicator_of_notMem (show 1 + y ∉ Ioi (1 : ℝ) by rw [Set.mem_Ioi]; linarith)]
  calc
    _ = ∫ y, (Ioi (0 : ℝ)).indicator (fun y => h (1 + y)) y := (integral_indicator measurableSet_Ioi).symm
    _ = ∫ y, (Ioi (1 : ℝ)).indicator h (1 + y) := congrArg (fun F : ℝ → ℂ => ∫ y, F y) hfun
    _ = ∫ t, (Ioi (1 : ℝ)).indicator h t :=
        integral_add_left_eq_self (fun t => (Ioi (1 : ℝ)).indicator h t) 1
    _ = ∫ t in Ioi (1 : ℝ), h t := integral_indicator measurableSet_Ioi

private lemma integral_one_add_cpow_neg {a : ℂ} (ha : 1 < a.re) :
  ∫ y in Ioi (0 : ℝ), ((1 + y : ℝ) : ℂ) ^ (-a) = 1 / (a - 1) := by
  have h1 : ∫ y in Ioi (0 : ℝ), ((1 + y : ℝ) : ℂ) ^ (-a) = ∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-a) :=
    setIntegral_Ioi_comp_one_add (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-a))
  rw [h1, integral_Ioi_cpow_of_lt (by rw [Complex.neg_re]; linarith) zero_lt_one, Complex.ofReal_one,
    Complex.one_cpow, show (-a + 1 : ℂ) = -(a - 1) by ring, div_neg, neg_div, neg_neg]

private lemma integral_radial {a : ℂ} (ha : 1 < a.re) :
  ∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-a) = 1 / (2 * (a - 1)) := by
  have hsub : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • ((1 + x ^ (2 : ℝ) : ℝ) : ℂ) ^ (-a) =
    ∫ y in Ioi (0 : ℝ), ((1 + y : ℝ) : ℂ) ^ (-a) :=
    integral_comp_rpow_Ioi (fun y : ℝ => ((1 + y : ℝ) : ℂ) ^ (-a)) two_ne_zero
  have hL : EqOn (fun x : ℝ => (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • ((1 + x ^ (2 : ℝ) : ℝ) : ℂ) ^ (-a))
    (fun x : ℝ => (2 : ℂ) * ((x : ℂ) * ((1 + x ^ 2 : ℝ) : ℂ) ^ (-a))) (Ioi (0 : ℝ)) := by
    intro x _
    simp only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, abs_two, Complex.real_smul]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hL, integral_const_mul, integral_one_add_cpow_neg ha] at hsub
  have hI : (∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-a)) =
    (2 : ℂ)⁻¹ * (2 * ∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-a)) := by ring
  rw [hI, hsub, one_div, one_div, ← mul_inv]

private lemma integral_value {s : ℂ} (hs : 0 < s.re) :
  ∫ z : ℂ, ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) = (Real.pi : ℂ) / (2 * s) := by
  have ha : 1 < (2 * s + 1).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re]
    linarith
  have hprod : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 : ℂ) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) * (1 : ℂ) ∂((volume : Measure ℝ).prod volume)) =
          (∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1))) *
        ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℂ) :=
    setIntegral_prod_mul (fun r : ℝ => (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)))
      (fun _ : ℝ => (1 : ℂ)) (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • ((1 + ‖Complex.polarCoord.symm p‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) :=
      (Complex.integral_comp_polarCoord_symm
        (fun z : ℂ => ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)))).symm
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          (p.1 : ℂ) * ((1 + p.1 ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) * (1 : ℂ)
            ∂((volume : Measure ℝ).prod volume) := by
        rw [Measure.volume_eq_prod]
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p _ => ?_
        rw [Complex.norm_polarCoord_symm, sq_abs, Complex.real_smul, mul_one]
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * ((1 + r ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1))) *
      ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := hprod
    _ = 1 / (2 * (2 * s + 1 - 1)) * ((2 * Real.pi : ℝ) : ℂ) := by
      rw [integral_radial ha, setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]),
        Complex.real_smul, mul_one]
      congr 1
      push_cast
      ring
    _ = (Real.pi : ℂ) / (2 * s) := by
      push_cast
      rw [div_mul_eq_mul_div, one_mul, show (2 : ℂ) * (2 * s + 1 - 1) = 2 * (2 * s) by ring,
        mul_div_mul_left _ _ (two_ne_zero : (2 : ℂ) ≠ 0)]
/--
[AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div.lean)
-/
@[path]
private lemma main
  {s : ℂ}
-- given
  (hs : 0 < s.re) :
-- imply
  ∫ z : ℂ, ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)) = (Real.pi : ℂ) / (2 * s) :=
-- proof
  integral_value hs


-- created on 2026-10-23
