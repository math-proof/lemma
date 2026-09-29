import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ} :
-- imply
  |∑ k ∈ Finset.range n, f k| ≤ ∑ k ∈ Finset.range n, |f k| := by
-- proof
  exact Finset.abs_sum_le_sum_abs _ _


-- created on 2026-09-27
