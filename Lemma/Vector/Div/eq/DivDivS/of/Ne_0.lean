import sympy.vector.Basic
import Lemma.Nat.Div.eq.HDiv
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Vector.GetDiv.eq.DivGetS
open Vector Rat Nat


@[main, comm]
private lemma main
  [CommGroupWithZero α]
  {a : α}
-- given
  (h : a ≠ 0)
  (x y : List.Vector α n) :
-- imply
  x / y = x / a / (y / a) := by
-- proof
  simp [HDiv.hDiv, Div.div]
  ext i
  repeat rw [GetDiv.eq.DivGetS.fin]
  simp [Div.eq.HDiv]
  rw [DivDivS.eq.Div.of.Ne_0 h]


-- created on 2025-12-17
