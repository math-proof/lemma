import sympy.tensor.Basic
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Algebra.Div.eq.DivDivS.of.Ne_0
import Lemma.Algebra.Div.eq.HDiv
open Vector Algebra


@[main, comm]
private lemma main
  [CommGroupWithZero α]
  {A : α}
-- given
  (h : A ≠ 0)
  (X Y : Tensor α s) :
-- imply
  X / Y = X / A / (Y / A) := by
-- proof
  simp [HDiv.hDiv, Div.div]
  ext i
  repeat rw [GetDiv.eq.DivGetS.fin]
  simp [Div.eq.HDiv]
  rw [DivDivS.eq.Div.of.Ne_0 h]


-- created on 2025-09-26
