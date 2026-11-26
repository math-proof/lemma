import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  (x : ℕ → ℤ) :
-- imply
  ∑ i < (n + 1), (x (i + 2) - x i) = x (n + 2) + x (n + 1) - x 0 - x 1 := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  induction n with
  | zero =>
    try simp only [Nat.Iio_eq_range] at *
    simp
    abel
  | succ n ih =>
    try simp only [Nat.Iio_eq_range] at *
    rw [Finset.sum_range_succ, ih]
    abel


-- created on 2020-03-24
-- updated on 2026-10-26
