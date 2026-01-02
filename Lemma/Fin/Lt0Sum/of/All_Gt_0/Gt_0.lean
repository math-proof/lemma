import Lemma.Finset.NeUnivEmpty.of.Gt_0
import Lemma.Finset.Lt0Sum.of.All_Gt_0.Ne_Empty
open Finset


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N]
  {x : Fin n → N}
-- given
  (h_n : n > 0)
  (h : ∀ i : Fin n, x i > 0) :
-- imply
  ∑ i : Fin n, x i > 0 := by
-- proof
  apply Lt0Sum.of.All_Gt_0.Ne_Empty (s := Finset.univ)
  ·
    apply NeUnivEmpty.of.Gt_0 h_n
  ·
    simpa


-- created on 2025-12-04
