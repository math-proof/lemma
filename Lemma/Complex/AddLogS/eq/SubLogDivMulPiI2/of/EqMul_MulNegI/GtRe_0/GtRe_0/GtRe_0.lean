import Mathlib
import sympy.Basic
open Complex
open scoped Real


private lemma exp_inj_of_im {x y : ℂ} (hx1 : -π < x.im) (hx2 : x.im ≤ π) (hy1 : -π < y.im) (hy2 : y.im ≤ π)
  (h : exp x = exp y) : x = y := by
  rw [← log_exp hx1 hx2, ← log_exp hy1 hy2, h]

private lemma arg_mem_of_re_pos {u : ℂ} (hu : 0 < u.re) : -(π / 2) < arg u ∧ arg u < π / 2 :=
  abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hu))

private lemma log_add_log_eq {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re)
  (h : u * v = -I * w) : log u + log v = log w - π * I / 2 := by
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hv0 : v ≠ 0 := fun h0 => by simp [h0] at hv
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  obtain ⟨hu1, hu2⟩ := arg_mem_of_re_pos hu
  obtain ⟨hv1, hv2⟩ := arg_mem_of_re_pos hv
  obtain ⟨hw1, hw2⟩ := arg_mem_of_re_pos hw
  have hpi := Real.pi_pos
  refine exp_inj_of_im ?_ ?_ ?_ ?_ ?_
  ·
    simp only [add_im, log_im]; linarith
  ·
    simp only [add_im, log_im]; linarith
  ·
    simp only [sub_im, log_im, div_ofNat_im, mul_im, ofReal_re, Complex.I_im, ofReal_im, Complex.I_re]; linarith
  ·
    simp only [sub_im, log_im, div_ofNat_im, mul_im, ofReal_re, Complex.I_im, ofReal_im, Complex.I_re]; linarith
  ·
    rw [exp_add, exp_log hu0, exp_log hv0, exp_sub, exp_log hw0, h,
      show π * I / 2 = (π / 2 : ℂ) * I by ring, exp_mul_I]
    have hc : Complex.cos (π / 2 : ℂ) = 0 := by exact_mod_cast Complex.cos_pi_div_two
    have hs : Complex.sin (π / 2 : ℂ) = 1 := by exact_mod_cast Complex.sin_pi_div_two
    rw [hc, hs]
    field_simp
    ring_nf
    simp
/--
[Complex_log_add_log_eq_log_sub_of_re_pos](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_log_add_log_eq_log_sub_of_re_pos.lean)
-/
@[path]
private lemma main
  {u v w : ℂ}
-- given
  (hu : 0 < u.re)
  (hv : 0 < v.re)
  (hw : 0 < w.re)
  (h : u * v = -Complex.I * w) :
-- imply
  Complex.log u + Complex.log v = Complex.log w - Real.pi * Complex.I / 2 :=
-- proof
  log_add_log_eq hu hv hw h


-- created on 2026-10-23
