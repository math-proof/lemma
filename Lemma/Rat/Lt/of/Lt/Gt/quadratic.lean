import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x m M a b c : ℝ}
  -- given
  (ha : 0 < a)
  (hm : m < x)
  (hM : x < M)
  -- imply
  : a * x ^ 2 + b * x + c < max (a * m ^ 2 + b * m + c) (a * M ^ 2 + b * M + c) := by
  -- proof
  set v := -b / (2 * a) with hv
  have ha2 : 0 < 2 * a := by linarith
  have hsq : (x - v) ^ 2 < max ((m - v) ^ 2) ((M - v) ^ 2) := by
    cases' le_total v x with hvx hvx
    · -- v ≤ x
      have h1 : (x - v) ^ 2 < (M - v) ^ 2 := by
        have h2 : 0 ≤ x - v := by linarith
        have h3 : x - v < M - v := by linarith
        nlinarith
      have h4 : (M - v) ^ 2 ≤ max ((m - v) ^ 2) ((M - v) ^ 2) := le_max_right _ _
      linarith
    · -- x ≤ v
      have h1 : (x - v) ^ 2 < (m - v) ^ 2 := by
        have h2 : 0 ≤ v - x := by linarith
        have h3 : v - x < v - m := by linarith
        nlinarith
      have h4 : (m - v) ^ 2 ≤ max ((m - v) ^ 2) ((M - v) ^ 2) := le_max_left _ _
      linarith
  have hmul : a * (x - v) ^ 2 < a * max ((m - v) ^ 2) ((M - v) ^ 2) :=
    mul_lt_mul_of_pos_left hsq ha
  have hmax : a * max ((m - v) ^ 2) ((M - v) ^ 2)
      = max (a * (m - v) ^ 2) (a * (M - v) ^ 2) := by
    rw [mul_max_of_nonneg]
    linarith
  rw [hmax] at hmul
  set k := c - b ^ 2 / (4 * a) with hk
  have hcex : ∀ t : ℝ, a * t ^ 2 + b * t + c = a * (t - v) ^ 2 + k := by
    intro t
    simp only [hv, hk]
    field_simp
    ring
  have hmax2 : max (a * (m - v) ^ 2) (a * (M - v) ^ 2) + k
      = max (a * (m - v) ^ 2 + k) (a * (M - v) ^ 2 + k) := by
    rw [max_add]
  have h6 : a * (x - v) ^ 2 + k
      < max (a * (m - v) ^ 2 + k) (a * (M - v) ^ 2 + k) := by
    linarith [hmax2]
  rw [hcex x, hcex m, hcex M]
  exact h6

-- created on 2019-12-19
