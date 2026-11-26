import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℕ → ℕ → ℝ}
  {f : ℕ → ℕ} :
-- imply
  ∑ i < 2, ∑ j < (f i), x i j = ∑ j < (f 0), x 0 j + ∑ j < (f 1), x 1 j := by
-- proof
  simp only [Nat.Iio_eq_range]
  simp [Finset.sum_range_succ]


-- created on 2026-09-27
-- updated on 2026-11-26
