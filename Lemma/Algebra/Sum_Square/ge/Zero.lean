import sympy.core.power
import Lemma.Basic


@[main]
private lemma main
  [DecidableEq ι]
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {s : Finset ι}
  {a : ι → α} :
-- imply
  ∑ i ∈ s, (a i)² ≥ 0 := by
-- proof
  -- Use the fact that the sum of non-negative terms is non-negative.
  refine' Finset.sum_nonneg _
  -- Introduce the index variable `i` for the sum.
  intro i _
  -- Each term in the sum is a square of a real number, hence non-negative.
  exact sq_nonneg _


-- created on 2025-04-06
