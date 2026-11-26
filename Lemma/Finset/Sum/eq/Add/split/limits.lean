import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℕ → ℂ} :
-- imply
  ∑ i < n, ∑ j < n, x i j =
    ∑ i < n, x i i +
      ∑ i < n, ∑ j < i, (x i j + x j i) := by
-- proof
  simp only [Nat.Iio_eq_range]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib] at *
    linear_combination ih


-- created on 2026-10-11
-- updated on 2026-11-26
