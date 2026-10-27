import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [AddCommMonoid β]
  {s : Finset ι}
  {x y : ι → β}
-- given
  (h : ∀ i ∈ s, x i = y i) :
-- imply
  ∑ i ∈ s, x i = ∑ i ∈ s, y i := by
-- proof
  rw [Finset.sum_congr rfl fun i hi => h i hi]


-- created on 2018-02-18
-- updated on 2026-10-26
