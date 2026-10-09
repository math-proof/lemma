import sympy.Basic


@[path]
private lemma main
  {S : Set α}
  {e : α}
-- given
  (h : e ∈ S) :
-- imply
  {e} ∪ S = S :=
-- proof
  Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr h)


-- created on 2020-07-11
