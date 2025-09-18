import Lemma.Set.Cup.eq.UnionCupS
import Lemma.Set.EqInterUnion
import Lemma.Set.EqSDiffUnion.of.Inter.eq.Empty
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ∩ B = ∅)
  (f : α → Set α) :
-- imply
  (⋃ x ∈ A, f x) ∪ ⋃ x ∈ B, f x = ⋃ x ∈ A ∪ B, f x := by
-- proof
  have := Cup.eq.UnionCupS f (A ∪ B) A
  rw [EqInterUnion] at this
  rw [EqSDiffUnion.of.Inter.eq.Empty h] at this
  symm at this
  assumption


-- created on 2025-07-20
