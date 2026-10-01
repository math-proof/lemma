import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e : ℤ}
  {s : Set ℤ}
-- given
  (h : e ∈ s) :
-- imply
  {e} ∩ s = {e} := by
-- proof
  exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr h)


-- created on 2020-10-28
