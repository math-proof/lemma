import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ∩ B = ∅) :
-- imply
  A \ B = A := by
-- proof
  apply Disjoint.sdiff_eq_left
  rwa [Set.disjoint_iff_inter_eq_empty]


-- created on 2019-01-31
-- updated on 2026-09-07
