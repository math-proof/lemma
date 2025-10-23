import Lemma.Algebra.Square.eq.Mul
import Lemma.Algebra.DivMul.eq.Mul_Div
import Lemma.Rat.DivMul.eq.MulDiv
import Lemma.Rat.DivDiv.eq.Div_Mul
open Algebra Rat


@[main]
private lemma main
  [DivisionCommMonoid α]
  {a b : α} :
-- imply
  (a / b)² = a² / b² := by
-- proof
  rw [Square.eq.Mul]
  rw [Mul_Div.eq.DivMul]
  rw [MulDiv.eq.DivMul]
  rw [Mul.eq.Square]
  rw [DivDiv.eq.Div_Mul]
  rw [Mul.eq.Square]


-- created on 2024-07-01
