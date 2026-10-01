import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f h g : ℕ → ℝ} :
-- imply
  ∑ i ∈ Finset.range n, (f i + h i) * g i = ∑ i ∈ Finset.range n, f i * g i + ∑ i ∈ Finset.range n, h i * g i := by
-- proof
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => add_mul _ _ _


-- created on 2020-03-27
