import sympy.Basic


@[main]
private lemma left
  {A B : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  A ∩ B = A :=
-- proof
  Set.inter_eq_self_of_subset_left h


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  B ∩ A = A :=
-- proof
  Set.inter_eq_self_of_subset_right h


-- created on 2025-05-18
-- updated on 2025-08-14
