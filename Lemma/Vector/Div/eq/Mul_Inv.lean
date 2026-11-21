import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.GetMul.eq.MulGet
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.Div.eq.Mul_Inv |
| comm | Vector.Mul_Inv.eq.Div |
-/
@[path, comm]
private lemma main
  [DivInvMonoid α]
-- given
  (X : List.Vector (List.Vector α n) m)
  (A : List.Vector α n) :
-- imply
  X / A = X * A⁻¹ := by
-- proof
  apply List.Vector.ext
  intro i
  rw [GetDiv.eq.DivGet.fin]
  rw [GetMul.eq.MulGet.fin]
  apply div_eq_mul_inv


-- created on 2025-09-24
-- updated on 2026-11-20
