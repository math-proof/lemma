import Lemma.Basic


@[main]
private lemma fin
  [DecidableEq α]
  {s t : Finset α} :
-- imply
  s \ t ∪ s ∩ t = s :=
-- proof
  Finset.sdiff_union_inter s t


@[main]
private lemma main
  {s t : Set α} :
-- imply
  s \ t ∪ s ∩ t = s :=
-- proof
  Set.diff_union_inter s t


-- created on 2025-04-08
