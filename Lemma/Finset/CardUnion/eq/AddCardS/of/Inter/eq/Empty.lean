import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {A B : Finset α}
-- given
  (h : A ∩ B = ∅) :
-- imply
  (A ∪ B).card = A.card + B.card :=
-- proof
  Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr h)


-- created on 2020-07-05
-- updated on 2026-09-07
