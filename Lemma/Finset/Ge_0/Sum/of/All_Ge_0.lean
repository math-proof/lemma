import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h : ∀ i ∈ Finset.range n, f i ≥ 0) :
-- imply
  ∑ i ∈ Finset.range n, f i ≥ 0 := by
-- proof
  exact Finset.sum_nonneg h


-- created on 2026-09-27
