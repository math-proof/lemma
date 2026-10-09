import sympy.Basic


@[path]
private lemma main
  {x y : ℤ}
  {n : ℕ} :
-- imply
  (x + y) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * x ^ k * y ^ (n - k) := by
-- proof
  rw [add_pow]
  exact Finset.sum_congr rfl fun k _ => by ring


-- created on 2020-10-10
