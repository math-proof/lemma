import sympy.Basic


@[main]
private lemma main
  [CommMonoid β]
  {s : Finset ι}
  {x y : ι → β}
-- given
  (h : ∀ i ∈ s, x i = y i) :
-- imply
  ∏ i ∈ s, x i = ∏ i ∈ s, y i := by
-- proof
  rw [Finset.prod_congr rfl fun i hi => h i hi]


-- created on 2025-07-29
