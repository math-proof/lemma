import Lemma.Nat.Mul
import Lemma.Vector.Dot.eq.SumMul
open Nat Vector


@[main]
private lemma Comm
  [CommMagma α] [AddCommMonoid α]
-- given
  (a b : List.Vector α n) :
-- imply
  a @ b = b @ a := by
-- proof
  rw [Dot.eq.SumMul, Dot.eq.SumMul, Mul.comm]


-- created on 2026-07-29
