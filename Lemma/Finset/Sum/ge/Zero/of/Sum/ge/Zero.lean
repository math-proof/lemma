import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℕ → ℝ}
-- given
  (h : ∀ i, ∑ j ∈ Finset.range n, f i j ≥ 0) :
-- imply
  ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n, f i j ≥ 0 := by
-- proof
  rw [Finset.sum_comm]
  exact Finset.sum_nonneg fun i _ => h i


-- created on 2020-03-26
