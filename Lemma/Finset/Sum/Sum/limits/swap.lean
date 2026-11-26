import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {m n : ℕ}
  (h : ℕ → ℝ)
  (g : ℕ → ℕ → ℝ) :
-- imply
  (∑ i < m, h i * (∑ j < n, g i j))
    = (∑ j < n, ∑ i < m, h i * g i j) := by
-- proof
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm


-- created on 2020-03-28
-- updated on 2026-10-26
