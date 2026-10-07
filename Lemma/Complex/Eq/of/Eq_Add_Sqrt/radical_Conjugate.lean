import Mathlib.Analysis.RCLike.Sqrt
import sympy.Basic


@[main]
private lemma main
  {x a d : ℂ}
-- given
  (h : Complex.sqrt (x ^ 2 + d) - x = a)
  (hd : d ≠ 0) :
-- imply
  x = (d / a - a) / 2 := by
-- proof
  have hsqr : Complex.sqrt (x ^ 2 + d) = x + a := by
    calc
      Complex.sqrt (x ^ 2 + d) = Complex.sqrt (x ^ 2 + d) - x + x := by ring
      _ = a + x := by rw [h]
      _ = x + a := by ring
  have hsq : (Complex.sqrt (x ^ 2 + d)) ^ 2 = x ^ 2 + d := by
    by_cases hz : x ^ 2 + d = 0
    · rw [hz, Complex.sqrt_zero, zero_pow (by norm_num)]
    · rw [sqrt_eq_exp hz, pow_two]
      rw [← Complex.exp_add, ← two_mul]
      have hlog : 2 * (Complex.log (x ^ 2 + d) / 2) = Complex.log (x ^ 2 + d) := by ring
      rw [hlog]
      exact Complex.exp_log hz
  have heq : x ^ 2 + d = (x + a) ^ 2 := by
    have hsq2 := congr_arg (fun y : ℂ => y ^ 2) hsqr
    rw [hsq] at hsq2
    exact hsq2
  have h1 : d = 2 * x * a + a ^ 2 := by
    calc
      d = x ^ 2 + d - x ^ 2 := by ring
      _ = (x + a) ^ 2 - x ^ 2 := by rw [heq]
      _ = 2 * x * a + a ^ 2 := by ring
  have ha : a ≠ 0 := by
    by_contra ha0
    have : d = 0 := by
      rw [ha0] at h1
      ring_nf at h1 ⊢
      exact h1
    exact hd this
  have h2 : 2 * a * x = d - a ^ 2 := by
    calc
      2 * a * x = 2 * x * a := by ring
      _ = d - a ^ 2 := by rw [h1]; ring
  calc
    x = (d - a ^ 2) / (2 * a) := by
      rw [eq_div_iff (show (2 * a : ℂ) ≠ 0 from mul_ne_zero (by norm_num) ha)]
      ring_nf at h2 ⊢
      exact h2
    _ = (d / a - a) / 2 := by field_simp [ha]


-- created on 2021-11-09
