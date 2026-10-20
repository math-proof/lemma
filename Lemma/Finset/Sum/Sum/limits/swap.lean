import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {m n : ℕ}
  (h : ℕ → ℝ)
  (g : ℕ → ℕ → ℝ) :
-- imply
  ∑ i ∈ Finset.range m, h i * ∑ j ∈ Finset.range n, g i j
    = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m, h i * g i j := by
-- proof
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm


-- created on 2020-03-28
-- updated on 2026-10-17
