import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  (x : ℕ → ℝ) :
-- imply
  ∑ i ∈ Finset.range 5, x i = x 0 + x 1 + x 2 + x 3 + x 4 := by
-- proof
  simp [Finset.sum_range_succ, add_assoc]


-- created on 2020-03-13
-- updated on 2026-10-17
