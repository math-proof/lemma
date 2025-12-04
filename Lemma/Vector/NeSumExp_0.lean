import Lemma.Nat.Ne.of.Gt
import Lemma.Vector.GtSumExp_0
open Vector Nat


@[main]
private lemma main
  [ExpPos α] [IsOrderedCancelAddMonoid α]
  [NeZero n]
-- given
  (x : List.Vector α n) :
-- imply
  (exp x).sum ≠ 0 := by
-- proof
  apply Ne.of.Gt
  apply GtSumExp_0


-- created on 2025-12-04
