import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : ∀ i, f i ≤ g i) :
-- imply
  ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range n, g i := by
-- proof
  exact Finset.sum_le_sum fun i _ => h i


-- created on 2019-11-16
