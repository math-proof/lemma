import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import sympy.vector.functions
open Nat Vector


@[main]
private lemma main
  [Exp α]
-- given
  (x : List.Vector (List.Vector α n) m) :
-- imply
  exp x.flatten = (exp x).flatten := by
-- proof
  ext t
  have h_t := t.isLt
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
  rw [GetExp.eq.ExpGet.fin]
  repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
  repeat rw [GetExp.eq.ExpGet.fin]


-- created on 2025-11-29
