import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {S : Finset α}
  {e : α}
-- given
  (h : e ∈ S) :
-- imply
  (S \ {e}).card = S.card - 1 := by
-- proof
  rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr h), Finset.card_singleton]


-- created on 2021-03-07
-- updated on 2023-06-01
