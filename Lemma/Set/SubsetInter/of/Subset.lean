import Lemma.Set.SubsetInter
import Lemma.Set.Subset.of.Subset.Subset
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B) 
  (S : Set α):
-- imply
  A ∩ S ⊆ B := by
-- proof
  apply Subset.of.Subset.Subset _ h
  apply SubsetInter.left


-- created on 2025-07-29
