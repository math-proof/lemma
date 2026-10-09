import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [DecidableEq ι]
  {A B : Finset ι}
  {f : ι → ℤ} :
-- imply
  ∑ k ∈ A \ B, f k + ∑ k ∈ A ∩ B, f k = ∑ k ∈ A, f k := by
-- proof
  rw [← Finset.sum_union (Finset.disjoint_sdiff_inter A B), Finset.sdiff_union_inter]


-- created on 2018-08-09
