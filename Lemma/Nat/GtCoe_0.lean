import Lemma.Nat.GtCoe_0.is.Gt_0
open Nat


@[main]
private lemma main
  [Semiring α] [PartialOrder α] [IsOrderedRing α]
  [Nontrivial α]
  [NeZero (d : ℕ)] :
-- imply
  (d : α) > 0 := by
-- proof
  apply GtCoe_0.of.Gt_0
  exact NeZero.pos d


-- created on 2025-11-07
