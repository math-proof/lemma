import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  -- imply
  : ∑ k ∈ Finset.Icc 1 n, 1 / ((k : ℝ) * ((k : ℝ) + 1))
    = 1 - 1 / ((n : ℝ) + 1) := by
  -- proof
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ n.succ)]
    rw [ih]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    have h_ident : ∀ (x : ℝ), x ≠ 0 → x + 1 ≠ 0 →
        1 - 1 / x + 1 / (x * (x + 1)) = 1 - 1 / (x + 1) := by
      intro x hx hxp
      field_simp [hx, hxp, mul_ne_zero hx hxp]
      ring
    simpa using h_ident ((n : ℝ) + 1) h1 h2

-- created on 2023-08-17
