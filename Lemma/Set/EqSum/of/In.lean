import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {m : ℕ}
  {y : ℕ → ℝ}
  {t : ℕ}
-- given
  (h : t ∈ Finset.range m) :
-- imply
  ∑ j < m, y j = (∑ j ∈ (Finset.range m).erase t, y j) + y t := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  exact (Finset.sum_erase_add _ _ h).symm


-- created on 2021-03-09
