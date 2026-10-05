import sympy.Basic
open Finset


@[main]
private lemma main
  [DecidableEq α]
  {A B : Finset α}
-- given
  (h : A ⊆ B) :
-- imply
  (B \ A).card = B.card - A.card :=
-- proof
  card_sdiff_of_subset h


-- created on 2021-06-26
-- updated on 2023-06-01
