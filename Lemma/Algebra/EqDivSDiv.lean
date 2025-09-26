import Lemma.Algebra.DivDiv.eq.Div_Mul
import Lemma.Algebra.Mul
open Algebra


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


@[main]
private lemma nat
-- given
  (a b c : ℕ) :
-- imply
  a / b / c = a / c / b := by
-- proof
  repeat rw [DivDiv.eq.Div_Mul.nat]
  rw [Mul.comm]


-- created on 2025-09-26
