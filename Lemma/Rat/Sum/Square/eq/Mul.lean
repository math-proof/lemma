import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 = n * (2 * n - 1) * (n - 1) / 6 := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring


-- created on 2023-12-13
