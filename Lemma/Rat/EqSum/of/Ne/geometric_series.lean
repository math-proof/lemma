import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {r : ℝ}
  {n : ℕ}
  -- given
  (hr : r ≠ 1)
  -- imply
  : ∑ k ∈ Finset.range n, r ^ k = (r ^ n - 1) / (r - 1) := by
  -- proof
  have hsub : r - 1 ≠ 0 := by
    intro h
    apply hr
    linarith
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp [hsub]
    ring

-- created on 2023-04-08
