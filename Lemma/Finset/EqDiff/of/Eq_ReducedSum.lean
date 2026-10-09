import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x xb : ℕ → ℝ}
-- given
  (h : ∀ n, xb n = (∑ k ∈ Finset.range n, x k) / n) :
-- imply
  xb (n + 1) - xb n = (x n - xb n) / (n + 1) := by
-- proof
  rw [h (n + 1), h n, Finset.sum_range_succ]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring


-- created on 2023-11-06
