import sympy.Basic


@[path]
private lemma main
  {m : ℕ}
  {I : ℕ → ℝ}
-- given
  (h₀ : ∀ k, k < m → I k = 0) :
-- imply
  ∑ k ∈ Finset.range m, I k = 0 := by
-- proof
  refine Finset.sum_eq_zero ?_
  intro k hk
  exact h₀ k (Finset.mem_range.mp hk)


-- created on 2026-10-11
-- updated on 2026-10-17
