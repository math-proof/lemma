import Lemma.Set.SDiff.eq.Empty.of.Subset
open Set


@[main]
private lemma main
-- given
  (A B : Set α) :
-- imply
  (A ∩ B) \ B = ∅ := by
-- proof
  apply SDiff.eq.Empty.of.Subset
  simp


-- created on 2025-07-20
