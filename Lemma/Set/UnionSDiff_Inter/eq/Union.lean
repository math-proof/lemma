import Lemma.Set.UnionSDiff.eq.SDiffUnion
import Lemma.Set.SDiffInter.eq.Empty
open Set


@[main]
private lemma main
-- given
  (A B : Set α) :
-- imply
  (A \ (A ∩ B)) ∪ B = A ∪ B := by
-- proof
  rw [UnionSDiff.eq.SDiffUnion]
  rw [SDiffInter.eq.Empty]
  simp


-- created on 2025-07-20
