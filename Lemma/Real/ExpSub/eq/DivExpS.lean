import sympy.functions.elementary.exponential
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Rat.Div.eq.Mul_Inv
open Int Rat


@[main, comm]
private lemma main
  [Exp R]
-- given
  (a b : R) :
-- imply
  exp (a - b) = exp a / exp b := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [Exp.exp_add]
  rw [Exp.exp_neg]
  rw [Div.eq.Mul_Inv]


-- created on 2025-10-04
