import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℕ → ℝ}
-- given
  (h : ∀ i, ∑ j < n, f i j ≥ 0) :
-- imply
  ∑ j < n, ∑ i < n, f i j ≥ 0 := by
-- proof
  rw [Finset.sum_comm]
  exact Finset.sum_nonneg fun i _ => h i


-- created on 2020-03-26
