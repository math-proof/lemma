import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import sympy.Basic

open Real


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≠ 0 ∨ y ≠ 0) :
-- imply
  Real.arccos (x / √(x ^ 2 + y ^ 2)) =
    if x ≥ 0 then
      Real.arcsin (|y| / √(x ^ 2 + y ^ 2))
    else
      π - Real.arcsin (|y| / √(x ^ 2 + y ^ 2)) := by
-- proof
  have h2 : 0 < x ^ 2 + y ^ 2 := by
    rcases h with h | h
    ·
      have hx := sq_pos_iff.mpr h
      have hy := sq_nonneg y
      linarith
    ·
      have hy := sq_pos_iff.mpr h
      have hx := sq_nonneg x
      linarith
  have hr : 0 < √(x ^ 2 + y ^ 2) := Real.sqrt_pos.mpr h2
  have hrq : (√(x ^ 2 + y ^ 2)) ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt h2.le
  have hst : (x / √(x ^ 2 + y ^ 2)) ^ 2 + (|y| / √(x ^ 2 + y ^ 2)) ^ 2 = 1 := by
    rw [div_pow, div_pow, sq_abs y, hrq]
    field_simp [hr.ne']
  have hnonneg : 0 ≤ |y| / √(x ^ 2 + y ^ 2) :=
    div_nonneg (abs_nonneg y) (Real.sqrt_nonneg (x ^ 2 + y ^ 2))
  have h1s2 : 1 - (x / √(x ^ 2 + y ^ 2)) ^ 2 = (|y| / √(x ^ 2 + y ^ 2)) ^ 2 := by
    linarith
  have hsqrt : √(1 - (x / √(x ^ 2 + y ^ 2)) ^ 2) = |y| / √(x ^ 2 + y ^ 2) := by
    rw [h1s2, Real.sqrt_sq hnonneg]
  by_cases hge : x ≥ 0
  ·
    have hps : 0 ≤ x / √(x ^ 2 + y ^ 2) :=
      div_nonneg hge (Real.sqrt_nonneg (x ^ 2 + y ^ 2))
    have hpi : Real.arccos (x / √(x ^ 2 + y ^ 2)) ≤ π / 2 := Real.arccos_le_pi_div_two.mpr hps
    have hsink : |y| / √(x ^ 2 + y ^ 2) = Real.sin (Real.arccos (x / √(x ^ 2 + y ^ 2))) := by
      rw [Real.sin_arccos, hsqrt]
    rw [if_pos hge, hsink]
    exact (Real.arcsin_sin
      (by linarith [Real.arccos_nonneg (x / √(x ^ 2 + y ^ 2)), Real.pi_pos]) hpi).symm
  ·
    have hge : x < 0 := not_le.mp hge
    have hns : x / √(x ^ 2 + y ^ 2) < 0 := div_neg_of_neg_of_pos hge hr
    have h1t2 : 1 - (|y| / √(x ^ 2 + y ^ 2)) ^ 2 = (x / √(x ^ 2 + y ^ 2)) ^ 2 := by
      linarith
    have hsqrt2 : √(1 - (|y| / √(x ^ 2 + y ^ 2)) ^ 2) = -(x / √(x ^ 2 + y ^ 2)) := by
      rw [h1t2, Real.sqrt_sq_eq_abs, abs_of_neg hns]
    have hcos : Real.cos (π - Real.arcsin (|y| / √(x ^ 2 + y ^ 2))) = x / √(x ^ 2 + y ^ 2) := by
      rw [Real.cos_pi_sub, Real.cos_arcsin, hsqrt2]
      ring
    have hv : 0 ≤ Real.arcsin (|y| / √(x ^ 2 + y ^ 2)) := Real.arcsin_nonneg.mpr hnonneg
    have hv2 : Real.arcsin (|y| / √(x ^ 2 + y ^ 2)) ≤ π / 2 :=
      Real.arcsin_le_pi_div_two (|y| / √(x ^ 2 + y ^ 2))
    have hθ : Real.arccos
        (Real.cos (π - Real.arcsin (|y| / √(x ^ 2 + y ^ 2)))) =
        π - Real.arcsin (|y| / √(x ^ 2 + y ^ 2)) :=
      Real.arccos_cos (by linarith [hv2, Real.pi_pos]) (by linarith [hv])
    rw [hcos] at hθ
    rw [if_neg (by linarith : ¬ x ≥ 0), hθ]


-- created on 2020-12-03
