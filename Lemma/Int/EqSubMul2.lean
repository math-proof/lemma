import Lemma.Nat.Mul2.eq.Add
import Lemma.Int.EqSubAdd
open Int Nat


@[main]
private lemma main
  [Ring α]
  {x : α} :
-- imply
  2 * x - x = x := by
-- proof
  rw [Mul2.eq.Add]
  rw [EqSubAdd]


-- created on 2025-05-04
-- updated on 2025-10-16
