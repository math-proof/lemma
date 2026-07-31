import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
open Nat


@[main]
private lemma Comm
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = a * c * b := by
-- proof
  repeat rw [Mul.comm (b := c)]
  rw [Mul_Mul.eq.MulMul]


@[main, comm]
private lemma rotate
  [CommSemigroup α]
-- given
  (a b c : α) :
-- imply
  a * b * c = b * c * a := by
-- proof
  rw [MulMul.eq.Mul_Mul]
  rw [Mul.comm]


-- created on 2024-11-29
-- updated on 2026-07-31
