import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma absorb
  {n : ℕ}
  {x : ℤ}
  {f : ℕ → ℤ} :
-- imply
  -(∑ k < n, f k) * x = -∑ k < n, f k * x := by
-- proof
  rw [neg_mul, Finset.sum_mul]


-- created on 2023-03-17
