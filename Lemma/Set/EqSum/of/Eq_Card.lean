import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [DecidableEq α] [AddCommMonoid β]
  {n : ℕ}
  {a : ℕ → α}
  {f : α → β}
-- given
  (h : ((Finset.range n).image a).card = n) :
-- imply
  ∑ x ∈ (Finset.range n).image a, f x = ∑ i < n, f (a i) := by
-- proof
  simp only [Nat.Iio_eq_range]
  apply Finset.sum_image
  exact Finset.card_image_iff.mp (h.trans (Finset.card_range n).symm)


-- created on 2021-03-20
-- updated on 2026-11-26
