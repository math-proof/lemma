import sympy.Basic


@[main, comm]
private lemma main
  (A B C : Set α) :
-- imply
  A ∩ B ∩ C = A ∩ (B ∩ C) :=
-- proof
  Set.inter_assoc A B C


-- created on 2024-12-21
