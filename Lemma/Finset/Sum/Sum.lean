import sympy.Basic


@[path]
private lemma limits.swap
  {m n : ℕ}
  {h : ℕ → ℝ}
  {g : ℕ → ℕ → ℝ} :
-- imply
  ∑ i ∈ Finset.range m, h i * ∑ j ∈ Finset.range n, g i j = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m, h i * g i j := by
-- proof
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm


-- created on 2026-09-27
