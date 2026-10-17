import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  (x : ℕ → ℤ) :
-- imply
  ∑ i ∈ Finset.range (n + 1), (x (i + 2) - x i) = x (n + 2) + x (n + 1) - x 0 - x 1 := by
-- proof
  induction n with
  | zero =>
    simp
    abel
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    abel


-- created on 2026-10-11
-- updated on 2026-10-17
