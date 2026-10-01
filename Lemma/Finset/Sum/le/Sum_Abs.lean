import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ} :
-- imply
  ∑ k ∈ Finset.range n, f k ≤ ∑ k ∈ Finset.range n, |f k| := by
-- proof
  exact Finset.sum_le_sum fun k _ => le_abs_self (f k)


-- created on 2026-09-27
