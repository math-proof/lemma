import Lemma.Set.EqInter.of.Subset
open Set


@[main]
private lemma main
-- given
  (A B : Set α) :
-- imply
  (A ∩ B) ∩ B = A ∩ B := by
-- proof
  apply EqInter.of.Subset.left
  simp


-- created on 2025-07-20
