import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {s t : Finset α} :
-- imply
  s \ t ∪ s ∩ t = s :=
-- proof
  Finset.sdiff_union_inter s t


-- created on 2025-12-30
