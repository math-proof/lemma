import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma gauss_summation
-- given
  (n : ℕ) :
-- imply
  ∑ i < n, i = n * (n - 1) / 2 := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  apply Finset.sum_range_id


-- created on 2024-12-21
-- updated on 2026-10-26
