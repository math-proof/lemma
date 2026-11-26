import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f h g : ℕ → ℝ} :
-- imply
  ∑ i < n, (f i + h i) * g i = ∑ i < n, f i * g i + ∑ i < n, h i * g i := by
-- proof
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => add_mul _ _ _


-- created on 2020-03-27
