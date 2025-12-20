import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [DecidableEq ι]
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {s : Finset ι}
  {a : ι → α} :
-- imply
  ∑ i ∈ s, (a i)² ≥ 0 := by
-- proof
  refine' Finset.sum_nonneg _
  intro i _
  exact sq_nonneg _


-- created on 2025-04-06
