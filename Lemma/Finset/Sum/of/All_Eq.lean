import sympy.Basic


@[main]
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


-- created on 2025-04-06
-- updated on 2025-12-01
