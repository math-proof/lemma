import Lemma.Nat.LtMulS.of.Lt.Lt.Ge_0.Ge_0
import Lemma.Nat.Square.eq.Mul
open Nat


@[main]
private lemma main
  [MonoidWithZero α] [LinearOrder α]
  [MulPosStrictMono α] [PosMulStrictMono α]
  {x y : α}
-- given
  (hy : y ≥ 0)
  (hgt : x > y) :
-- imply
  x² > y² := by
-- proof
  rw [Square.eq.Mul, Square.eq.Mul]
  exact GtMulS.of.Gt.Gt.Ge_0.Ge_0 hy hy hgt hgt


-- created on 2018-07-07
