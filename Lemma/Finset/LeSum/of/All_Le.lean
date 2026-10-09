import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : ∀ i ∈ Finset.range n, f i ≤ g i) :
-- imply
  ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range n, g i := by
-- proof
  exact Finset.sum_le_sum h


-- created on 2019-01-26
