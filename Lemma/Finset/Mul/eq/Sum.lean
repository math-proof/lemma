import sympy.sets.sets
import sympy.Basic


@[path]
private lemma as_multiple_limits
  {n m : ℕ}
  {f g : ℕ → ℤ} :
-- imply
  (∑ i ∈ Finset.range m, f i) * ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i * g j := by
-- proof
  exact Finset.sum_mul_sum _ _ _ _


-- created on 2020-02-02
