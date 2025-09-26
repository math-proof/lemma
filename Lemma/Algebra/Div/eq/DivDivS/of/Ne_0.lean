import Lemma.Algebra.DivDiv.eq.Div_Mul
import Lemma.Algebra.EqMul_Div.of.Ne_0
open Algebra


@[main, comm]
private lemma main
  [CommGroupWithZero α]
  {a : α}
-- given
  (h : a ≠ 0)
  (x y : α) :
-- imply
  x / y = x / a / (y / a) := by
-- proof
  rw [DivDiv.eq.Div_Mul]
  conv_rhs =>
    arg 2
    rw [EqMul_Div.of.Ne_0 h]


-- created on 2025-09-26
