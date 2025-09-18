import Lemma.Set.SubsetInter
import Lemma.Set.SubsetInter.of.Subset
import Lemma.Set.Inter
import Lemma.Set.Subset_Inter.of.Subset.Subset
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B)
  (S : Set α) :
-- imply
  A ∩ S ⊆ B ∩ S := by
-- proof
  have h := SubsetInter.of.Subset h S
  have := SubsetInter.left S A
  rw [Inter.comm] at this
  apply Subset_Inter.of.Subset.Subset h this


-- created on 2025-07-29
