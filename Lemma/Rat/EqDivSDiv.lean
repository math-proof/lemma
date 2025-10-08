import Lemma.Rat.DivDiv.eq.Div_Mul
import Lemma.Algebra.Mul
open Algebra Rat


@[main]
private lemma main
  [DivisionCommMonoid α]
-- given
  (a b c : α) :
-- imply
  a / b / c = a / c / b := by
-- proof
  repeat rw [DivDiv.eq.Div_Mul]
  rw [Mul.comm]


-- created on 2025-09-26
-- updated on 2025-10-08
