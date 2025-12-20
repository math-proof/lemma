import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Rat.EqMul_Div.of.Ne_0
import Lemma.Rat.InvDiv.eq.Div
open Rat


@[main]
private lemma main
  [CommGroupWithZero α]
-- given
  (h : a ≠ 0)
  (b : α) :
-- imply
  a / (a / b) = b := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [InvDiv.eq.Div]
  rw [EqMul_Div.of.Ne_0 h]


-- created on 2025-12-20
