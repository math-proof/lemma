import Lemma.Set.InterSDiff_Inter.eq.Empty
import Lemma.Set.UnionCupS.eq.Cup.of.Inter.eq.Empty
import Lemma.Set.UnionSDiff_Inter.eq.Union
import Lemma.Set.InterSDiff.eq.Empty
import Lemma.Set.EqUnionSDiff_Inter
import Lemma.Set.UnionUnion
import Lemma.Set.EqUnion.of.Subset
import Lemma.Set.Subset_Union.of.Subset
import Lemma.Set.SubsetCupS.of.Subset
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (f : α → Set α) :
-- imply
  (⋃ x ∈ A, f x) ∪ ⋃ x ∈ B, f x = ⋃ x ∈ A ∪ B, f x := by
-- proof
  have := InterSDiff_Inter.eq.Empty A B
  have := UnionCupS.eq.Cup.of.Inter.eq.Empty this f
  rw [UnionSDiff_Inter.eq.Union A B] at this
  rw [← this]
  have h := UnionCupS.eq.Cup.of.Inter.eq.Empty (InterSDiff.eq.Empty A (A ∩ B)) f
  rw [EqUnionSDiff_Inter A B] at h
  rw [← h]
  rw [UnionUnion.comm]
  apply EqUnion.of.Subset.left
  apply Subset_Union.of.Subset
  apply SubsetCupS.of.Subset
  simp


-- created on 2025-07-20
