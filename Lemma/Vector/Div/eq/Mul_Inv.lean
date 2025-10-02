import sympy.vector.vector
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Algebra.Div.eq.Mul_Inv
open Vector Algebra


@[main, comm]
private lemma main
  [DivInvMonoid α]
-- given
  (X : List.Vector (List.Vector α n) m)
  (A : List.Vector α n) :
-- imply
  X / A = X * A⁻¹ := by
-- proof
  ext i j
  rw [GetDiv.eq.DivGet.fin]
  rw [GetMul.eq.MulGet.fin]
  rw [Div.eq.Mul_Inv]


-- created on 2025-09-24
