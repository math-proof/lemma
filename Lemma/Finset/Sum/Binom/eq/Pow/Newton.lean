import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℤ}
  {n : ℕ} :
-- imply
  ∑ k < (n + 1), (n.choose k : ℤ) * x ^ k * y ^ (n - k) = (x + y) ^ n := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  rw [add_pow]
  exact Finset.sum_congr rfl fun k _ => by ring


-- created on 2021-11-25
