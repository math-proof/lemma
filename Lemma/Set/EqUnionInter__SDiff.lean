import sympy.Basic


@[main]
private lemma main
-- given
  (s t : Set α) :
-- imply
  s ∩ t ∪ s \ t = s :=
-- proof
  Set.inter_union_sdiff s t


-- created on 2025-04-30
-- updated on 2025-07-20
