import Mathlib.Algebra.BigOperators.Module
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  (f g : ℕ → ℝ) :
-- imply
  ∑ k ∈ Finset.range (n + 1), f k * g k
    = f n * ∑ k ∈ Finset.range (n + 1), g k
      - ∑ k ∈ Finset.range n,
        (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i := by
-- proof
  simpa [smul_eq_mul] using Finset.sum_range_by_parts f g (n + 1)


-- created on 2023-06-02
-- updated on 2026-10-17
