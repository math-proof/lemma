import Lemma.Set.InterSDiff.eq.Empty.of.SubsetInter
open Set


@[main]
private lemma main
-- given
  (A B : Set α) :
-- imply
  (A \ (A ∩ B)) ∩ B = ∅ := by
-- proof
  apply InterSDiff.eq.Empty.of.SubsetInter
  simp


-- created on 2025-07-20
