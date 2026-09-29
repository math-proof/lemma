import sympy.Basic


@[main]
private lemma main
  [DecidableEq α] [AddCommMonoid β]
  {n : ℕ}
  {a : ℕ → α}
  {f : α → β}
-- given
  (h : ((Finset.range n).image a).card = n) :
-- imply
  ∑ x ∈ (Finset.range n).image a, f x = ∑ i ∈ Finset.range n, f (a i) := by
-- proof
  apply Finset.sum_image
  exact Finset.card_image_iff.mp (h.trans (Finset.card_range n).symm)


-- created on 2026-09-27
