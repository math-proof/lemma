import Lemma.Set.InterSDiff.eq.SDiffInterS
import Lemma.Set.SDiff.eq.Empty.of.Subset
import Lemma.Set.Subset_Inter.of.Subset.Subset
open Set


@[main]
private lemma main
  {A B C : Set α}
-- given
  (h : A ∩ B ⊆ C) :
-- imply
  (A \ C) ∩ B = ∅ := by
-- proof
  rw [InterSDiff.eq.SDiffInterS]
  rw [SDiff.eq.Empty.of.Subset]
  apply Subset_Inter.of.Subset.Subset
  ·
    assumption
  ·
    simp


-- created on 2025-07-20
