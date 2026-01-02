import Lemma.Fin.Lt0Sum.of.All_Gt_0.Gt_0
import Lemma.Nat.Ne.of.Gt
open Fin Nat


@[main]
private lemma main
  [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N]
  {x : Fin n → N}
-- given
  (h_n : n ≠ 0)
  (h : ∀ i : Fin n, x i > 0) :
-- imply
  ∑ i : Fin n, x i ≠ 0 := by
-- proof
  apply Ne.of.Gt
  apply Lt0Sum.of.All_Gt_0.Gt_0 _ h
  omega


-- created on 2025-12-04
