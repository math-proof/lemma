import Mathlib.Algebra.Field.GeomSum
import sympy.Basic


@[path]
private lemma main
  {lam : ℝ}
  {n : ℕ}
-- given
  (h₀ : |lam| < 1) :
-- imply
  ∑ k ∈ Finset.range n, lam ^ k = (lam ^ n - 1) / (lam - 1) := by
-- proof
  have hne : lam ≠ 1 := by
    intro h
    simp [h] at h₀
  simpa using geom_sum_eq hne n


-- created on 2023-10-08
-- updated on 2026-10-17
