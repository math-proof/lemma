import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {h : ℕ → ℝ}
-- given
  (h₀ : ∀ k < n, h k ≤ 0) :
-- imply
  ∑ k ∈ Finset.range n, h k ≤ 0 := by
-- proof
  exact Finset.sum_nonpos (fun k hk => h₀ k (Finset.mem_range.mp hk))


-- created on 2026-09-27
