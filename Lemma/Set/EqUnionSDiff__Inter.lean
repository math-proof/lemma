import sympy.Basic


@[main]
private lemma main
  {s t : Set α} :
-- imply
  s \ t ∪ s ∩ t = s :=
-- proof
  Set.diff_union_inter s t


-- created on 2025-04-08
