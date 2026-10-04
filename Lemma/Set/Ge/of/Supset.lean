import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {A B : Finset α}
-- given
  (h : A ⊇ B) :
-- imply
  A.card ≥ B.card :=
-- proof
  Finset.card_le_card h


-- created on 2021-07-03
