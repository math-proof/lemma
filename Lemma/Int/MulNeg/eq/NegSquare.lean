import Lemma.Int.NegMul.eq.MulNeg
import Lemma.Nat.Square.eq.Mul
open Int Nat


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
