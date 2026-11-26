import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n i : ℕ} :
-- imply
  ∑ k < n, (i + k).choose i = (n + i).choose (i + 1) := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  induction n with
  | zero =>
    try simp only [Nat.Iio_eq_range] at *
    simp
  | succ n ih =>
    try simp only [Nat.Iio_eq_range] at *
    rw [Finset.sum_range_succ, ih, show n + 1 + i = (n + i) + 1 by omega, Nat.choose_succ_succ, add_comm i n, add_comm]


-- created on 2023-06-03
