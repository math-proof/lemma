import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {A B : Finset α} :
-- imply
  (A ∪ B).card ≥ A.card :=
-- proof
  Finset.card_le_card Finset.subset_union_left


-- created on 2026-09-27
