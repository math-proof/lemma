import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ∑ k < n, (k : ℝ) ^ 2 = n * (2 * n - 1) * (n - 1) / 6 := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  induction n with
  | zero => simp
  | succ n ih =>
    try simp only [Nat.Iio_eq_range] at *
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring


-- created on 2023-12-13
