import sympy.sets.sets
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
  -- Use the fact that the sum of non-negative terms is non-negative.
  refine' Finset.sum_le_sum fun i hi => _
  -- Apply the given inequality for each i in the range.
  exact h i hi


-- created on 2025-04-06
