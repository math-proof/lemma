import Lemma.Algebra.Square.eq.Mul
import Lemma.Algebra.Mul_Neg.eq.NegMul
open Algebra


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
