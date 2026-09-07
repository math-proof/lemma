import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {A B : Finset α} :
-- imply
  (A ∪ B).card ≤ A.card + B.card :=
-- proof
  Finset.card_union_le A B


-- created on 2020-07-06
-- updated on 2026-09-07
