import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ} :
-- imply
  ∑ i < n, f (i + 1) = ∑ i ∈ Finset.Ico 1 (n + 1), f i := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  induction n with
  | zero =>
    try simp only [Nat.Iio_eq_range] at *
    simp
  | succ n ih =>
    try simp only [Nat.Iio_eq_range] at *
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top (show 1 ≤ n + 1 by omega)]


-- created on 2021-12-29
-- updated on 2026-10-26
