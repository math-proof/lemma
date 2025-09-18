import Lemma.Algebra.NegMul.eq.MulNeg
import Lemma.Algebra.Square.eq.Mul
open Algebra


@[main]
private lemma main
  [Ring α]
  {a : α} :
-- imply
  -a * a = -a² := by
-- proof
  rw [
    MulNeg.eq.NegMul,
    Mul.eq.Square
  ]


-- created on 2024-11-29
