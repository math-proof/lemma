import Lemma.Nat.Ge.of.Le
import Lemma.Nat.LeMulS.of.Le.Le.Ge_0.Ge_0
import Lemma.Nat.Square.eq.Mul
open Nat


@[main]
private lemma main
  [MonoidWithZero α] [LinearOrder α]
  [MulPosMono α] [PosMulMono α]
  {x y : α}
-- given
  (hx : x ≥ 0)
  (h : x ≤ y) :
-- imply
  x² ≤ y² := by
-- proof
  rw [Square.eq.Mul, Square.eq.Mul]
  have hy : y ≥ 0 := ge_trans (Ge.of.Le h) hx
  exact LeMulS.of.Le.Le.Ge_0.Ge_0 hy hx h h


-- created on 2018-07-03
