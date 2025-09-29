import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x y : ℕ → ℝ}
-- given
  (h₀ : ∀ i ∈ range n, x i ≤ y i) :
-- imply
  ∑ i ∈ range n, x i ≤ ∑ i ∈ range n, y i := by
-- proof
  -- Use the fact that the sum of non-negative terms is non-negative.
  refine' Finset.sum_le_sum fun i hi => _
  -- Apply the given inequality for each i in the range.
  exact h₀ i hi


-- created on 2025-04-06
