import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {h : ℕ → ℝ}
-- given
  (h₀ : ∀ k < n, h k ≤ 0) :
-- imply
  ∑ k ∈ Finset.range n, h k ≤ 0 := by
-- proof
  exact Finset.sum_nonpos (fun k hk => h₀ k (Finset.mem_range.mp hk))


-- created on 2019-12-06
