import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ} :
-- imply
  ∑ k < n, f k ≤ ∑ k < n, |f k| := by
-- proof
  exact Finset.sum_le_sum fun k _ => le_abs_self (f k)


-- created on 2023-04-15
