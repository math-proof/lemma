import sympy.Basic


@[path]
private lemma main
  {A B : Set α} :
-- imply
  A ∪ B = A ∪ (B \ A) :=
-- proof
  Set.union_sdiff_self.symm


-- created on 2020-08-08
