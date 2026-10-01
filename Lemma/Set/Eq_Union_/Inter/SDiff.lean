import sympy.Basic


@[main]
private lemma main
  {A B : Set α} :
-- imply
  A = A ∩ B ∪ A \ B :=
-- proof
  (Set.inter_union_sdiff A B).symm


-- created on 2020-10-05
