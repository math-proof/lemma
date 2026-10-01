import sympy.sets.sets
import sympy.Basic


@[main]
private lemma absorb
  {n : ℕ}
  {x : ℤ}
  {f : ℕ → ℤ} :
-- imply
  -(∑ k ∈ Finset.range n, f k) * x = -∑ k ∈ Finset.range n, f k * x := by
-- proof
  rw [neg_mul, Finset.sum_mul]


-- created on 2023-03-17
