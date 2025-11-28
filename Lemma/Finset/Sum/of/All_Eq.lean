import sympy.sets.sets
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
  -- We use the fact that the sum of a sequence is uniquely determined by its elements.
  -- Since for all i in the range n, x i = y i, we can directly substitute x with y in the sum.
  rw [Finset.sum_congr rfl fun i hi => h i hi]


@[main]
private lemma fin
  [AddCommMonoid β]
  {x y : Fin n → β}
-- given
  (h : ∀ i : Fin n, x i = y i) :
-- imply
  ∑ i : Fin n, x i = ∑ i : Fin n, y i := by
-- proof
  apply main
  aesop


-- created on 2025-04-06
-- updated on 2025-04-26
