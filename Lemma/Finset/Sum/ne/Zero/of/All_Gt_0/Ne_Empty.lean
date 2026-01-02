import Lemma.Finset.Lt0Sum.of.All_Gt_0.Ne_Empty
import Lemma.Nat.Ne.of.Gt
open Finset Nat


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N]
  {s : Finset ι}
  {x : ι → N}
-- given
  (h_s : s ≠ ∅)
  (h : ∀ i ∈ s, x i > 0) :
-- imply
  ∑ i ∈ s, (x i) ≠ 0 := by
-- proof
  apply Ne.of.Gt
  apply Lt0Sum.of.All_Gt_0.Ne_Empty h_s h


-- created on 2025-12-04
