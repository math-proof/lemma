import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N]
  {s : Finset ι}
  {x y : ι → N}
-- given
  (h : ∀ i ∈ s, x i ≤ y i) :
-- imply
  ∑ i ∈ s, x i ≤ ∑ i ∈ s, y i := by
-- proof
  refine Finset.sum_le_sum fun i hi => ?_
  exact h i hi


-- created on 2025-04-06
