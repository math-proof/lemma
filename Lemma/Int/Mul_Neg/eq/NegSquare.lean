import Lemma.Nat.Square.eq.Mul
import Lemma.Int.Mul_Neg.eq.NegMul
open Nat Int


@[main]
private lemma main
  [Ring α]
  {a : α} :
-- imply
  a * -a = -a² := by
-- proof
  rw [Mul_Neg.eq.NegMul]
  rw [Mul.eq.Square]


-- created on 2024-11-29
