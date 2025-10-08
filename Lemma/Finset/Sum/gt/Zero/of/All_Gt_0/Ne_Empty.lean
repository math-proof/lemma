import Lemma.Finset.GtSumS.of.All_Gt.Ne_Empty
open Finset


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N]
  {s : Finset ι}
  {x : ι → N}
-- given
  (h_s : s ≠ ∅)
  (h : ∀ i ∈ s, x i > 0) :
-- imply
  ∑ i ∈ s, (x i) > 0 := by
-- proof
  have := GtSumS.of.All_Gt.Ne_Empty (x := x) (y := fun _ => 0) h_s h
  simp at this
  assumption


-- created on 2025-10-08
