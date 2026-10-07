import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {r : ℝ}
  {n : ℕ}
  -- imply
  : ∑ k ∈ Finset.range n, r ^ k = if r = 1 then (n : ℝ) else (1 - r ^ n) / (1 - r) := by
  -- proof
  by_cases hr : r = 1
  · rw [if_pos hr]
    rw [hr]
    simp [Finset.sum_const]
  · rw [if_neg hr]
    have hsub : r - 1 ≠ 0 := by
      intro h
      apply hr
      linarith
    have h1 : ∑ k ∈ Finset.range n, r ^ k = (r ^ n - 1) / (r - 1) := by
      exact geom_sum_eq hr n
    rw [h1]
    have h2 : (1 - r) ≠ 0 := by
      intro h
      apply hr
      linarith
    field_simp [hsub, h2]
    ring

-- created on 2023-06-17
