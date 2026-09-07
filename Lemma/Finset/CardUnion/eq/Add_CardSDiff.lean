import Lemma.Finset.CardUnion.eq.AddCardS.of.Inter.eq.Empty
open Finset


@[main]
private lemma main
  [DecidableEq α]
  {A B : Finset α} :
-- imply
  (A ∪ B).card = (A \ B).card + B.card := calc
-- proof
  _ = ((A \ B) ∪ B).card := by
    rw [← sdiff_union_self_eq_union]
  _ = (A \ B).card + B.card :=
    CardUnion.eq.AddCardS.of.Inter.eq.Empty (by simp)


-- created on 2020-07-05
-- updated on 2026-09-07
