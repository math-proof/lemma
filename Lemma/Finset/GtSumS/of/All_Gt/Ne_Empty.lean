import Lemma.Finset.Any.of.All.Ne_Empty
import Lemma.Finset.GtSumS.of.Any_Gt.All_Ge
import Lemma.Finset.All_Ge.of.All_Gt
open Finset


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N]
  {s : Finset ι}
  {x y : ι → N}
-- given
  (h_s : s ≠ ∅)
  (h : ∀ i ∈ s, x i > y i) :
-- imply
  ∑ i ∈ s, (x i) > ∑ i ∈ s, (y i) := by
-- proof
  have h_any := Any.of.All.Ne_Empty h_s h
  have h := All_Ge.of.All_Gt h
  apply GtSumS.of.Any_Gt.All_Ge h h_any


-- created on 2025-10-08
