import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f h : ℕ → ℝ} :
-- imply
  ∏ i < n, (f i - h i) = (∏ i < n, -(f i - h i)) * (-1) ^ n := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  induction n with
  | zero => simp
  | succ n ih =>
    try simp only [Nat.Iio_eq_range] at *
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
    ring


-- created on 2023-06-03
