import sympy.Basic


@[path]
private lemma main
  [DecidableEq α] [AddCommMonoid β]
  {n : ℕ}
  {a : ℕ → α}
  {f : α → β}
-- given
  (h : ((Finset.range n).image a).card = n) :
-- imply
  ∑ x ∈ (Finset.range n).image a, f x = ∑ i : Fin n, f (a i) := by
-- proof
  rw [Finset.sum_image (Finset.card_image_iff.mp (h.trans (Finset.card_range n).symm))]
  exact Finset.sum_range fun i => f (a i)


-- created on 2022-01-10
