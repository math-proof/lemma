import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {r : ℝ}
  {n : ℕ}
  -- given
  (hr : r ≠ 1)
  -- imply
  : ∑ k < n, r ^ k = (r ^ n - 1) / (r - 1) := by
  -- proof
  try simp only [Nat.Iio_eq_range] at *
  have hsub : r - 1 ≠ 0 := by
    intro h
    apply hr
    linarith
  induction n with
  | zero =>
    try simp only [Nat.Iio_eq_range] at *
    simp
  | succ n ih =>
    try simp only [Nat.Iio_eq_range] at *
    rw [Finset.sum_range_succ, ih]
    field_simp [hsub]
    ring

-- created on 2023-04-08
