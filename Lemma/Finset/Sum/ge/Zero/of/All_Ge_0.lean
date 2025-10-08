import Lemma.Finset.GeSumS.of.All_Ge
open Finset


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N]
  {s : Finset ι}
  {x : ι → N}
-- given
  (h : ∀ i ∈ s, x i ≥ 0) :
-- imply
  ∑ i ∈ s, (x i) ≥ 0 := by
-- proof
  have := GeSumS.of.All_Ge (x := x) (y := fun _ => 0) h
  simp at this
  assumption


-- created on 2025-04-06
