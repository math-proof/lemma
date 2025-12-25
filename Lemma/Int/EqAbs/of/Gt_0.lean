import Lemma.Int.EqAbs.is.Ge_0
import Lemma.Nat.Ge.of.Gt
open Int Nat


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  |x| = x := by
-- proof
  apply EqAbs.of.Ge_0
  apply Ge.of.Gt h


-- created on 2025-10-01
-- updated on 2025-12-25
